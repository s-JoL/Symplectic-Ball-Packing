"""Arb enclosures for the *infinite* theta Fermat parametrization.

Matches paper/supp/cubic-bundle.tex and Bundle/Theta.lean. All lattice
constants are computed as balls, including g3; no binary Gamma period or
fixed theta truncation is used. Curvature uses a sum of squared wedges,
which avoids subtracting two large positive Gram terms.
"""
from dataclasses import dataclass
import math

from flint import arb, acb, acb_series, ctx


@dataclass
class CubicValues:
    raw: tuple
    derivative: tuple
    norm_squared: arb
    density: arb
    connection: tuple


class CertifiedCubic:
    def __init__(self, bits=128):
        self.bits = bits
        with ctx.workprec(bits):
            self.pi = arb.pi()
            self.imtau = arb(3).sqrt()/2
            self.tau = acb(-arb(1)/2, self.imtau)
            g2, g3 = self.tau.elliptic_invariants()
            if not g2.contains(0) or not g3.imag.contains(0) or not g3.real > 0:
                raise ArithmeticError('equianharmonic invariants could not be enclosed')
            # Reality is a lattice-conjugation identity, g2=0 follows from
            # hexagonal symmetry (the cited paper/Lean lemmas).
            self.g3 = g3.real
            self.cF = 1/self.g3.root(3)
            self.dF = 1/(3*self.g3).sqrt()
            self.ratio = {}
            for conjugate in (False, True):
                tau = -self.tau.conjugate() if conjugate else self.tau
                t = acb_series([0, 1], prec=6).modular_theta(tau)[0]
                self.ratio[conjugate] = 2*t[3]/t[1]

    def _raw(self, z, conjugate=False):
        tau = -self.tau.conjugate() if conjugate else self.tau
        t = acb_series([z, 1], prec=6).modular_theta(tau)[0]
        # Arb's argument includes pi. These are z derivatives, so pi^2
        # and pi^3 are already included in P and Q.
        t0, t1, t2, t3, t4 = [t[j]*math.factorial(j) for j in range(5)]
        ratio = self.ratio[conjugate]
        P = t1*t1*t0-t2*t0*t0+ratio*t0**3
        Q = -t3*t0*t0+3*t1*t2*t0-2*t1**3
        dP = t1**3-t3*t0*t0+3*ratio*t0*t0*t1
        dQ = -t4*t0*t0+t1*t3*t0+3*t2*t2*t0-3*t1*t1*t2
        Z = (2*self.cF*P, -t0**3-self.dF*Q, -t0**3+self.dF*Q)
        dZ = (2*self.cF*dP, -3*t0*t0*t1-self.dF*dQ, -3*t0*t0*t1+self.dF*dQ)
        return Z, dZ

    def _taylor_box(self, z, order=24, conjugate=False):
        """Enclose Z, Z', and their wedges using analytic Taylor models.

        Expanding the full polynomial in theta jets before substituting an
        input box prevents the enormous dependency inflation of evaluating
        those polynomials directly on a box. The omitted coefficients are
        bounded by Cauchy's inequality on a larger complex disk.
        """
        previous_cap = ctx.cap
        ctx.cap = max(previous_cap, order+5)
        try:
            return self._taylor_box_impl(z, order, conjugate)
        finally:
            ctx.cap = previous_cap

    def _taylor_box_impl(self, z, order, conjugate):
        centre = z.mid()
        dz = z-centre
        radius = abs(dz).upper()
        R = max(4*radius, arb('0.01')).lower()
        tau = -self.tau.conjugate() if conjugate else self.tau
        t = acb_series([centre, 1], prec=order+5).modular_theta(tau)[0]
        t1, t2, t3 = t.derivative(), t.derivative().derivative(), t.derivative().derivative().derivative()
        P = t1*t1*t-t2*t*t+self.ratio[conjugate]*t**3
        Q = -t3*t*t+3*t1*t2*t-2*t1**3
        Zs = (2*self.cF*P, -t**3-self.dF*Q, -t**3+self.dF*Q)
        Ds = tuple(s.derivative() for s in Zs)
        Ws = tuple(Zs[i]*Ds[j]-Zs[j]*Ds[i] for i in range(3) for j in range(i+1, 3))
        if min(s.prec for s in (*Zs, *Ds, *Ws)) < order+1:
            raise ArithmeticError('Taylor series was truncated below its claimed remainder order')
        circle_box = centre+acb(arb(0, R), arb(0, R))
        outerZ, outerD = self._raw(circle_box, conjugate)
        Mz, Md = max(abs(x).upper() for x in outerZ), max(abs(x).upper() for x in outerD)
        ratio = radius/R
        factor = ratio**(order+1)/(1-ratio)
        def enclose(series, bound):
            value = acb(0)
            for k in range(order, -1, -1):
                value = value*dz+series[k]
            error = (bound*factor).upper()
            return value+acb(arb(0, error), arb(0, error))
        return (tuple(enclose(s, Mz) for s in Zs), tuple(enclose(s, Md) for s in Ds),
                tuple(enclose(s, 2*Mz*Md) for s in Ws))

    def evaluate(self, u, v):
        """Valid for points and whole real coordinate boxes on the cover."""
        with ctx.workprec(self.bits):
            u, v = arb(u), arb(v)
            z = acb(u)+self.tau*v
            if u.is_exact() and v.is_exact():
                Z, dZ = self._raw(z)
                wedges = tuple(Z[i]*dZ[j]-Z[j]*dZ[i] for i in range(3) for j in range(i+1, 3))
            else:
                Z, dZ, wedges = self._taylor_box(z)
            norm = sum(abs(z)**2 for z in Z)
            wedge = sum(abs(w)**2 for w in wedges)
            density = self.imtau/self.pi*wedge/norm**2
            inner = sum(z.conjugate()*dz for z, dz in zip(Z, dZ))/norm
            eta = (inner.imag/(2*self.pi)+3*v,
                   (self.tau*inner).imag/(2*self.pi)+3*u-arb(3)*v/2-arb(1)/2)
            return CubicValues(Z, dZ, norm, density, eta)

    def analytic_forms(self, u, v):
        """Meromorphic complexification for rigorous acb.integral callbacks.

        Conjugating the integration variable would invalidate Arb's
        analytic flag. Instead evaluate the conjugate theta SERIES at
        u+conj(tau)*v, with coefficients conjugated via -conj(tau).
        Returns (eta_u, eta_v, rho), all holomorphic in complex u,v away
        from the explicitly evaluated norm denominator.
        """
        with ctx.workprec(self.bits):
            return self._analytic_forms(u, v)

    def _analytic_forms(self, u, v):
        u, v = acb(u), acb(v)
        def data(z, conjugate=False):
            if max(z.real.rad(), z.imag.rad()) > arb(2)**(-self.bits//2):
                return self._taylor_box(z, conjugate=conjugate)
            Z, D = self._raw(z, conjugate)
            W = tuple(Z[i]*D[j]-Z[j]*D[i] for i in range(3) for j in range(i+1, 3))
            return Z, D, W
        Z, dZ, W = data(u+self.tau*v)
        if u.imag.is_zero() and v.imag.is_zero():
            C, dC = tuple(x.conjugate() for x in Z), tuple(x.conjugate() for x in dZ)
            WC = tuple(x.conjugate() for x in W)
        else:
            C, dC, WC = data(u+self.tau.conjugate()*v, conjugate=True)
        norm = sum(z*c for z, c in zip(Z, C))
        plus = sum(c*dz for c, dz in zip(C, dZ))/norm
        minus = sum(z*dc for z, dc in zip(Z, dC))/norm
        eta_u = (plus-minus)/(4*self.pi*acb(0, 1))+3*v
        eta_v = (self.tau*plus-self.tau.conjugate()*minus)/(4*self.pi*acb(0, 1))+3*u-arb(3)*v/2-arb(1)/2
        wedge = sum(w*wc for w, wc in zip(W, WC))
        rho = self.imtau/self.pi*wedge/norm**2
        return eta_u, eta_v, rho

    def unit_lift_A(self, u, v):
        with ctx.workprec(self.bits):
            u, v = arb(u), arb(v)
            value = self.evaluate(u, v)
            phase = (acb(0, 1)*self.pi*(6*u*v-arb(3)*v*v/2-v)).exp()
            return tuple(z/value.norm_squared.sqrt()*phase for z in value.raw)
