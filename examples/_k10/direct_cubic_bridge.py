"""Certified primitives and CDF inverse of the actual cubic form.

The optional Fourier object supplies Newton starting guesses only. Every
returned root is enclosed using a residual and the independently certified
global derivative lower bound. No Fourier approximation defines this map.

Coordinates x=u+v,y=v. A=eta_u, B=eta_v-eta_u, rho=B_x-A_y.
R=integral_0^x rho(s-y,y)ds, M=R(1,y), H=integral_0^1 A(s,y)ds.
Then V=y-(H(y)-H(0))/3, U=R/M, G=integral_0^x A(s,y)ds+integral_0^y B(0,t)dt.
Thus eta=dG+R dy=dG+3U dV exactly.
"""
import json
import math
from .arb_cache import floor_mid,nearest_mid
from pathlib import Path

from flint import arb, acb, ctx
from .certified_cubic import CertifiedCubic
from .complex_quadrature import integrate as complex_integral


class _QuadratureCubic(CertifiedCubic):
    """Use direct interval algebra on tiny boxes, Taylor models on wide ones.

    Both evaluate the identical inherited theta formulas with Arb bounds.
    Quadrature point nodes with a tiny real parameter uncertainty do not
    need an order-24 theta Taylor model at every function evaluation.
    Wide complex ellipse boxes retain the original Cauchy remainder model.
    """
    def _taylor_box(self,z,order=24,conjugate=False):
        if max(z.real.rad(),z.imag.rad())<arb(2)**-40:
            Z,D=self._raw(z,conjugate)
            W=tuple(Z[i]*D[j]-Z[j]*D[i] for i in range(3) for j in range(i+1,3))
            return Z,D,W
        return super()._taylor_box(z,order,conjugate)


class DirectCubicBridge:
    def __init__(self, bits=128, root_bits=72, certificate=None, workers=16, verified_normal=True):
        self.bits, self.root_bits = bits, root_bits
        self.workers = workers
        self._normal_cache = {}
        self._verified_cache = {}
        self.verified_normal = verified_normal
        self._guess_bridge = None
        if bits < root_bits+32:
            raise ValueError('insufficient guard precision for certified roots')
        self.cubic = _QuadratureCubic(bits)
        if certificate is None:
            certificate = Path(__file__).with_name('data.json')
        report = json.loads(Path(certificate).read_text())['cubic_certificate']
        if not report.get('passed') or report['density_lower'] <= 0:
            raise ValueError('a positive whole-torus curvature certificate is required')
        # The source hash links the bounds to the evaluated formula.
        import hashlib
        kernel = Path(__file__).with_name('certified_cubic.py')
        if hashlib.sha256(kernel.read_bytes()).hexdigest() != report['kernel_sha256']:
            raise ValueError('cubic certificate does not match the current evaluator')
        self.rho_lower = arb(report['density_lower'])
        # Exact reflection/hexagonal identities, not rounded integrals.
        # See examples/README.md, "Cubic normalization", and the included
        # paper/supp/cubic-bundle.tex theta lift and deck identities.
        self.H0, self.G01 = arb(0), arb(-2)
        self.cu, self.cv = .5, 1.5
        self.punctures = (0., 1/3, 2/3)

    def integral(self, function, endpoint, parameter_radius=0):
        with ctx.workprec(self.bits):
            # Parameter/endpoint balls cause unavoidable output width.
            # Asking quadrature to beat that width exhausts its subdivision
            # budget. A looser stopping goal does not loosen its enclosure.
            tolerance = max(arb(2)**(-self.root_bits-24),
                            2**22*(arb(parameter_radius)+arb(endpoint).rad()))
            # Short panels keep the complex norm denominator away from its
            # non-real zeros in the analytic quadrature ellipses.
            endpoint_ball=arb(endpoint)
            end = acb(endpoint_ball.mid())
            panels = max(1, math.ceil(float(abs(end).upper())*8))
            value = acb(0)
            for j in range(panels):
                value += complex_integral(lambda s, analytic: function(s), end*j/panels,
                                      end*(j+1)/panels, rel_tol=tolerance,
                                      abs_tol=tolerance/panels, eval_limit=max(20000,self.bits**3),
                                      deg_limit=max(32,2*self.bits),depth_limit=max(30,self.bits))
            # Complex quadrature uses fixed endpoints. The real endpoint
            # uncertainty is a separate FTC remainder; feeding a whole
            # endpoint ball to acb.integral can prevent convergence even
            # when every real integrand value is regular.
            if not endpoint_ball.rad().is_zero():
                value+=(endpoint_ball-endpoint_ball.mid())*function(acb(endpoint_ball))
            if not value.is_finite() or not value.imag.contains(0):
                raise ArithmeticError(f'certified real integral failed: {value}')
            return value.real

    def H(self, y):
        with ctx.workprec(self.bits):
            y = self._fraction(y)[1]
            return self.integral(lambda s: self.cubic.analytic_forms(s-acb(y), y)[0], 1, y.rad())

    @staticmethod
    def _fraction(value):
        value = arb(value)
        integer = floor_mid(value)
        return integer, value-integer

    def R(self, x, y):
        with ctx.workprec(self.bits):
            n, x = self._fraction(x)
            y = self._fraction(y)[1]
            value = self.integral(lambda s: self.cubic.analytic_forms(s-acb(y), y)[2], x, y.rad())
            return value+n*self.M(y) if n else value

    def M(self, y):
        with ctx.workprec(self.bits):
            y = self._fraction(y)[1]
            return self.integral(lambda s: self.cubic.analytic_forms(s-acb(y), y)[2], 1, y.rad())

    def V(self, y):
        with ctx.workprec(self.bits):
            y = arb(y)
            return y-(self.H(y)-self.H0)/3

    def vertical_G(self, y):
        with ctx.workprec(self.bits):
            y = arb(y)
            return -y/2-3*y*y/2

    def G(self, x, y):
        with ctx.workprec(self.bits):
            n, x = self._fraction(x)
            reduced_y = self._fraction(y)[1]
            value = self.integral(lambda s: self.cubic.analytic_forms(s-acb(reduced_y), reduced_y)[0], x, reduced_y.rad())
            return value+n*self.H(reduced_y)+self.vertical_G(y)

    @staticmethod
    def _enclose_root(centre, residual, derivative_lower):
        radius = (abs(residual)/derivative_lower).upper()
        return arb(centre, radius)

    def _monotone_inverse(self,value,derivative,target,guess,lower,goal):
        """Safeguarded inversion for a global increasing map with value(0)=0.

        Newton chooses fast proposals, while bracket contraction guarantees
        progress independently of the numerical initial guess. Residual
        enclosures, rather than the bracket alone, retain input uncertainty.
        """
        target,lower,goal=arb(target),arb(lower),arb(goal)
        if not lower>0:raise ValueError('a positive global derivative bound is required')
        if target.is_zero():return arb(0)
        lo=min(arb(0),(target.lower()/lower.lower()).lower())
        hi=max(arb(0),(target.upper()/lower.lower()).upper())
        centre=arb(guess).mid()
        if not lo<centre<hi:centre=((lo+hi)/2).mid()
        for iteration in range(max(128,16*self.bits)):
            residual=value(centre)-target
            if not residual.is_finite():raise ArithmeticError('nonfinite scalar inverse residual')
            root=self._enclose_root(centre,residual,lower)
            if root.rad()<goal or residual.contains(0):return root
            if residual>0:hi=min(hi,centre)
            elif residual<0:lo=max(lo,centre)
            slope=derivative(centre)
            candidate=(centre-residual/slope).mid() if slope>0 else ((lo+hi)/2).mid()
            # Allow Newton arbitrarily close to a bracket endpoint: the
            # root often lies there after a sign update. One forced
            # bisection in eight steps still guarantees bracket progress.
            if not lo<=candidate<=hi or iteration%8==7:candidate=((lo+hi)/2).mid()
            if candidate==centre:return root
            centre=candidate
        raise ArithmeticError('safeguarded scalar inverse exhausted its refinement budget')

    def inverse_base(self, U, V, guess=None):
        """Enclose (old_u,old_v) for the unique exact CDF inverse."""
        with ctx.workprec(self.bits):
            U, V = arb(U), arb(V)
            nU, U = self._fraction(U)
            nV, V = self._fraction(V)
            x0, y0 = (U.mid(), V.mid()) if guess is None else map(arb, guess)
            if guess is not None:
                x0, y0 = (x0-nU).mid(), (y0-nV).mid()
            target = arb(2)**(-self.root_bits)
            # Guard y more tightly: uncertainty in y enters the x equation.
            y_target = target/2**16
            y=self._monotone_inverse(self.V,lambda t:self.M(t)/3,V,y0,self.rho_lower/3,y_target)
            mass = self.M(y)
            x=self._monotone_inverse(lambda t:self.R(t,y),
                lambda t:self.cubic.evaluate(t-y,y).density,U*mass,x0,self.rho_lower,target)
            return (nU+x)-(nV+y),nV+y

    def old_normal_input(self, U, V, q, p, d, guess=None):
        """Enclose the exact homogeneous normal initial state (Z,W).

        Inputs use the reference flat frame cu=1/2,cv=3/2. A constant
        symplectic base translation matches its clutch to the actual CDF
        frame; it preserves the fibre moment identically.
        """
        with ctx.workprec(self.bits):
            U, V, fibre = arb(U), arb(V), acb(q, p)
            alpha = (self.cv-arb(3)/2)/3
            beta = (arb(1)/2-self.cu)/3
            # (U,V,z)->(U+alpha,V+beta,exp(2pi i 9alpha V)z).
            fibre *= (acb(0, 18)*self.cubic.pi*alpha*V).exp()
            u, v = self.inverse_base(U+alpha, V+beta, guess)
            x = u+v
            fibre *= (acb(0, 6)*self.cubic.pi*self.G(x, v)).exp()
            Z = self.cubic.unit_lift_A(u, v)
            moment = self.cubic.pi*abs(fibre)**2
            d = arb(d)
            if not d-moment > 0:
                raise ValueError('normal input is not certified below d')
            W = self.cubic.pi.sqrt()*fibre/(d-moment).sqrt()
            return (*Z, W), dict(u=u, v=v, moment=moment, alpha=alpha, beta=beta)
