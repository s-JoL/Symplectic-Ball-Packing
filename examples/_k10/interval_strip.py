"""Validated primitives for the disk-to-strip chart.

This uses real Taylor quadrature across the flat seams, residual enclosures
for monotone scalar inverses, and the same exact chart as DiskStrip.
"""
import math

from flint import arb, arb_series, ctx
from .interval_bump import step_jet
from .verified_quadrature import integrate
from .implicit_series import solve as implicit_series


def integer_power(value, n):
    result = value*0+1
    while n:
        if n % 2:
            result *= value
        value *= value
        n //= 2
    return result


def _integral_panel(job):
    rho, delta, bits, tolerance, kind, b, zm, upper, right, index, count = job
    with ctx.workprec(bits):
        integer_M = None
        if isinstance(kind, tuple):
            kind, integer_M = kind
        strip = IntervalStrip(arb(rho), arb(delta), bits, tolerance, workers=1, integer_M=integer_M)
        b, upper = arb(b), arb(upper)
        if isinstance(index, str):
            left, end = arb(index), arb(count)
        else:
            left, end = upper*index/count, upper*(index+1)/count
        if kind == 'area':
            value = strip._area_serial(b, left, end)
        elif kind == 'cap':
            value = integrate(lambda t: strip._cap_integrand(b, t, right), left, end,
                    tolerance=tolerance, bits=bits, order=strip.order, strict_radius=False).value
        else:
            zm = arb(zm)
            value = integrate(lambda phi: strip.kernel(b, phi, zm, right)[2], left, end,
                    tolerance=tolerance, bits=bits, order=strip.order, strict_radius=False).value
        return value.str(bits)


class IntervalStrip:
    def __init__(self, rho, delta, bits=256, tolerance='1e-45', workers=1, integer_M=None):
        self.bits, self.tolerance = bits, tolerance
        self.workers = workers
        self.order = max(24, (bits//128)*16-16)
        with ctx.workprec(bits):
            self.rho, self.delta = arb(rho), arb(delta)
            self.c, self.mu = self.delta/4, self.delta/8
            self.V0 = self.rho+self.delta
            self.M = (math.ceil(math.nextafter(float((2*self.V0/self.delta).upper()), math.inf))
                      if integer_M is None else int(integer_M))
            if not self.M*self.delta >= 2*self.V0:
                raise ValueError('strip integer does not satisfy its required lower bound')
            self.t0 = self.c.sqrt()/4
            self.sigma = 4*self.t0
            self.eta = self.c/(4*self.V0)
            self.z0 = arb(1)/4
            self.local_b = min(self.t0*self.t0, self.mu*self.z0*self.z0)
            self.area_scale = arb.pi()*self.sigma/(2*self.mu.sqrt())
            self.local_w = self.area_scale*self.local_b
            self.scale = (2*(self.c*self.mu).sqrt()).sqrt()
            self._primitive_cache = {}

    def potential(self, z):
        argument = (z*z/(self.z0*self.z0)-1)/3
        return self.mu*z*z+self.V0*integer_power(z, 2*self.M)*step_jet(argument)

    def potential_prime(self, z):
        argument = (z*z/(self.z0*self.z0)-1)/3
        return (2*self.mu*z+self.V0*(2*self.M*integer_power(z, 2*self.M-1)*step_jet(argument)
                +integer_power(z, 2*self.M)*step_jet(argument, 1)*2*z/(3*self.z0*self.z0)))

    def Xprime(self, t, side=None):
        if side is None:
            if abs(t[0]).upper() <= self.t0:
                return t*0+self.sigma
            if t[0] > 0:
                side = 1
                y = t
            elif t[0] < 0:
                side = self.eta
                y = -t
            else:
                raise ValueError('Xprime interval spans both noncentral branches')
        else:
            side = arb(side)
            y = t  # explicit side: caller supplies the nonnegative radius
        argument = (y*y/(self.t0*self.t0)-1)/3
        S = step_jet(argument)
        return self.sigma*(1-S)+2*side*y*S

    def F(self, y, side=1):
        """Enclose the exact primitive F(y)=integral_0^y Xprime(s) ds."""
        with ctx.workprec(self.bits):
            y, side = arb(y), arb(side)
            if not y.lower() >= 0:
                raise ValueError('F expects a nonnegative real interval')
            if y.upper() <= self.t0:
                return self.sigma*y
            def dyadic_ball(value):
                return tuple((str(x.man_exp()[0]), int(x.man_exp()[1])) for x in (value.mid(), value.rad()))
            key = (dyadic_ball(side), dyadic_ball(y))
            if key not in self._primitive_cache:
                value = integrate(lambda s: self.Xprime(s, side), 0, y,
                    bits=self.bits, tolerance=self.tolerance, order=self.order, strict_radius=False).value
                self._primitive_cache[key] = value
            return self._primitive_cache[key]

    def local(self, q, p):
        """The exact central linear branch, including its domain check."""
        with ctx.workprec(self.bits):
            q, p = arb(q), arb(p)
            if not arb.pi()*(q*q+p*p) < self.local_w:
                raise ValueError('point not certified in the central linear chart')
            return self.c+self.scale*q, arb(1)/2+p/self.scale

    def X(self, t):
        t = arb(t)
        if abs(t).upper() <= self.t0:
            return self.c+self.sigma*t
        if t > 0:
            return self.c+self.F(t)
        if t < 0:
            return self.c-self.F(-t, self.eta)
        raise ValueError('refine X across its central collar')

    def inverse_X(self, x):
        x = arb(x)
        if abs(x-self.c).upper() <= self.sigma*self.t0:
            return (x-self.c)/self.sigma
        lower = min(self.sigma.lower(), (2*self.eta*self.t0).lower())
        guess = (x-self.c)/self.sigma
        left, right = -max(arb(1), abs(guess).upper()), max(arb(1), abs(guess).upper())
        while not self.X(left).upper() < x.lower(): left *= 2
        while not self.X(right).lower() > x.upper(): right *= 2
        return self._solve(self.X,
            lambda t:self.Xprime(arb_series([t],prec=1))[0],x,guess,lower,left,right)

    def _swept_area(self, b, upper, right):
        """Half integral of z(t) X'(t) dt, from the orbit's right tip.

        The sine substitution is the same regularized real integral used
        for area(), and avoids quadrature of a quadrature for X itself.
        """
        if upper.is_zero():return arb(0)
        def integrand(phi):
            si,co = phi.sin(),phi.cos()
            energy=b*si*si
            z=(b/self.mu).sqrt()*si if energy[0].upper() <= self.mu*self.z0*self.z0 else self._area_root(b,si)
            return b.sqrt()*z*self.Xprime(b.sqrt()*co,1 if right else self.eta)*si/2
        return integrate(integrand,0,upper,bits=self.bits,tolerance=self.tolerance,
                         order=self.order,strict_radius=False).value

    def inverse(self, x, T, *, with_action=False):
        """Inverse strip chart, optionally also its forward primitive.

        dS = X dT - (q dp-p dq)/2. Quadrant formulas retain a complete
        orbit's area, so the action is continuous across the phase axes.
        """
        with ctx.workprec(self.bits):
            x,T=arb(x),arb(T)
            q,p=(x-self.c)/self.scale,(T-arb(1)/2)*self.scale
            if (arb.pi()*(q*q+p*p)).upper() < self.local_w.lower():
                result=(q,p)
                return (result,self.c*p/self.scale+q*p/2) if with_action else result
            t=self.inverse_X(x)
            z=2*T-1
            b=t*t+self.potential(arb_series([z],prec=1))[0]
            if not b > 0: raise ValueError('refine the inverse strip energy near zero')
            zm=self.root_z(b)
            w=self.area(b)
            Pr=self.quarter_time(b,arb.pi()/2,True,zm,full=True)
            Pl=self.quarter_time(b,arb.pi()/2,False,zm,full=True)
            period=2*(Pr+Pl)
            # The identity V(z)<=b proves that this ratio is in [0,1].
            ratio=abs(z)/zm
            lo,hi=max(arb(0),ratio.lower()),min(arb(1),ratio.upper())
            if hi < lo: raise ArithmeticError('strip orbit violates its defining energy')
            phi=arb((lo+hi)/2,(hi-lo)/2).asin()
            points=[]; actions=[]
            for right in (True,False):
                if right and t.upper()<0 or not right and t.lower()>0:continue
                Q=self.quarter_time(b,phi,right,zm)
                for upper in (True,False):
                    if upper and z.upper()<0 or not upper and z.lower()>0:continue
                    theta=(Q/period if right and upper else
                           arb(1)/2-Q/period if upper else
                           arb(1)/2+Q/period if not right else 1-Q/period)
                    radius=(w/arb.pi()).sqrt()
                    angle=2*arb.pi()*theta
                    points.append((radius*angle.cos(),radius*angle.sin()))
                    if with_action:
                        # psi parametrizes t=sqrt(b)cos(psi), including
                        # both endpoints where the potential is quadratic.
                        r=abs(t)/b.sqrt()
                        rlo,rhi=max(arb(0),r.lower()),min(arb(1),r.upper())
                        psi=arb((rlo+rhi)/2,(rhi-rlo)/2).acos()
                        part=x*abs(z)/2+(1 if right else -1)*self._swept_area(b,psi,right)
                        orbit=part if right and upper else w/2+part if upper else w/2-part if not right else w-part
                        actions.append(orbit-w*theta)
            if not points:raise ArithmeticError('no inverse strip quadrant')
            result=points[0]
            for point in points[1:]:result=tuple(a.union(b) for a,b in zip(result,point))
            if not with_action:return result
            action=actions[0]
            for value in actions[1:]:action=action.union(value)
            return result,action

    def root_z(self, energy, target=None):
        """Certified positive root of V(z)=energy; no sampled monotonicity."""
        with ctx.workprec(self.bits):
            energy = arb(energy)
            target = arb(self.tolerance)/2**48 if target is None else arb(target)
            if not target>0:raise ValueError('a positive root-refinement goal is required')
            if not energy > 0:
                raise ValueError('root_z requires positive energy')
            if not energy.is_exact():
                return self.root_z(energy.lower(), target).union(self.root_z(energy.upper(), target))
            lower = min((energy.lower()/(2*self.mu)).sqrt().lower(),
                        (energy.lower()/(2*self.V0)).root(2*self.M).lower())
            derivative_lower = 2*self.mu*lower
            upper = (energy.upper()/self.mu).sqrt().upper()
            centre = min((energy.mid()/self.mu).sqrt(),
                         (energy.mid()/self.V0).root(2*self.M)).mid()
            for iteration in range(max(64,16*self.bits)):
                jet = arb_series([centre, 1], prec=2)
                value = self.potential(jet)
                residual = value[0]-energy
                radius = (abs(residual)/derivative_lower).upper()
                root = arb(centre, radius)
                # A roundoff-limited residual already encloses the root.
                # Returning that verified ball lets the outer accuracy
                # check request more precision; endlessly chasing a goal
                # below this arithmetic's resolution cannot improve it.
                if radius<target or residual.contains(0):
                    return root
                if residual > 0:
                    upper = min(upper, centre)
                elif residual < 0:
                    lower = max(lower, centre)
                candidate = (centre-residual/value[1]).mid()
                centre = (candidate if candidate>lower and candidate<upper and iteration%8!=7
                          else ((lower+upper)/2).mid())
            raise ArithmeticError('potential root was not enclosed to the requested radius')

    def root_z_jet(self, energy):
        constant = self.root_z(energy[0])
        def equation(z,size):
            target=arb_series([energy[j] for j in range(size)],prec=size)
            return self.potential(z)-target,self.potential_prime(z)
        return implicit_series(constant,energy.prec,equation,2*self.mu*constant.lower())

    def area(self, energy):
        """Exact area, integrated without nested X-primitives.

        A(b)=sqrt(b) integral_0^(pi/2) zmax(b sin^2 phi)
                 [X'(sqrt(b)cos phi)+X'(-sqrt(b)cos phi)] sin phi dphi.
        """
        with ctx.workprec(self.bits):
            if self.workers > 1:
                return self._parallel_integral('area', arb(energy), None, arb.pi()/2, True)
            return self._area_serial(arb(energy), 0, arb.pi()/2)

    def _parallel_integral(self, kind, b, zm, upper, right):
        from concurrent.futures import ProcessPoolExecutor
        import multiprocessing as mp
        # Put separate jobs inside the extremely thin turning-point caps.
        # The cuts only select a mesh; all integrals retain rigorous real
        # remainders, so floating mesh positions do not define the map.
        maximum = float(upper.mid())
        b0, t0, z0 = float(b.mid()), float(self.t0.mid()), float(self.z0.mid())
        cuts = [0., maximum]
        if kind == 'cap':
            cut = float(self.t0.mid())
            if 0 < cut < maximum:
                cuts.append(cut)
        elif kind == 'time':
            for target in (4*t0*t0, t0*t0):
                if b0 > target:
                    cap = self.root_z(arb(b0-target))
                    angle = math.asin(min(1., max(0., float(cap.mid())/float(zm.mid()))))
                    if 0 < angle < maximum:
                        cuts.append(angle)
        else:
            for target in (2*t0, t0):
                ratio = target/math.sqrt(b0)
                if ratio < 1:
                    angle = math.acos(ratio)
                    if 0 < angle < maximum:
                        cuts.append(angle)
            for z in (z0, 2*z0):
                E = self.potential(arb_series([arb(z)], prec=1))[0]
                ratio = float(E.mid())/b0
                if 0 < ratio < 1:
                    angle = math.asin(math.sqrt(ratio))
                    if 0 < angle < maximum:
                        cuts.append(angle)
        cuts = sorted(set(cuts))
        endpoints = [arb(value) for value in cuts]
        endpoints[-1] = upper
        segments = []
        pieces = self.workers*2
        for left, end in zip(endpoints[:-1], endpoints[1:]):
            segments.extend([(left+(end-left)*i/pieces, left+(end-left)*(i+1)/pieces)
                             for i in range(pieces)])
        count = len(segments)
        jobs = [(self.rho.str(self.bits), self.delta.str(self.bits), self.bits,
                 (arb(self.tolerance)/count).str(self.bits), (kind, self.M), b.str(self.bits),
                 zm.str(self.bits) if zm is not None else None, upper.str(self.bits), right,
                 left.str(self.bits), end.str(self.bits)) for left, end in segments]
        with ProcessPoolExecutor(self.workers, mp_context=mp.get_context('spawn')) as pool:
            values = list(pool.map(_integral_panel, jobs))
        return sum(arb(value) for value in values)

    def _area_serial(self, energy, left, upper):
        with ctx.workprec(self.bits):
            b = arb(energy)
            if not b > 0:
                raise ValueError('area requires positive energy')
            def integrand(phi):
                si, co = phi.sin(), phi.cos()
                E = b*si*si
                if E[0].upper() <= self.mu*self.z0*self.z0:
                    zm = b.sqrt()/self.mu.sqrt()*si
                elif E[0].lower()>4*self.mu*self.z0*self.z0:
                    # Beyond the small quadratic cap, direct implicit
                    # jets retain the narrow z constant and avoid
                    # expanding the correlated product (R*sin(phi))^2M.
                    zm=self.root_z_jet(E)
                else:
                    zm = self._area_root(b, si)
                t = b.sqrt()*co
                return b.sqrt()*zm*(self.Xprime(t)+self.Xprime(-t))*si
            return integrate(integrand, left, upper, tolerance=self.tolerance,
                             bits=self.bits, order=self.order, strict_radius=False).value

    def _area_root(self, b, sine):
        """Factor zmax(b sin^2 phi)=R(phi) sin(phi) before taking jets.

        The naive implicit sqrt jet loses the cancellation between sin^2
        and sqrt near the low-energy cap. R is nearly constant there.
        Its constant enclosure uses b/(mu+V0*z^(2M-2)*S), so parameter
        correlation is also preserved in the leading interval.
        """
        energy = b*sine[0]*sine[0]
        zbox = self.root_z(energy)
        argument = (zbox*zbox/(self.z0*self.z0)-1)/3
        S = step_jet(arb_series([argument], prec=1))[0]
        zpower = zbox**(2*self.M-2)
        denominator=self.mu+self.V0*zpower*S
        lo,hi=max(self.mu.lower(),denominator.lower()),denominator.upper()
        if hi<lo:raise ArithmeticError('factored root contradicts its positive denominator')
        denominator=arb((lo+hi)/2,(hi-lo)/2)
        r0 = (b/denominator).sqrt()
        # d/dr [mu r^2+V0 r^2 (r sin)^(2M-2) S]>=2mu*r.
        def equation(R,size):
            s=arb_series([sine[j] for j in range(size)],prec=size);z=R*s
            z[0]=z[0].intersection(zbox)
            argument=(z*z/(self.z0*self.z0)-1)/3
            S=step_jet(argument);Sp=step_jet(argument,1)
            power=integer_power(z,2*self.M-2)
            residual=self.mu*R*R+self.V0*R*R*power*S-b
            derivative=2*self.mu*R+self.V0*(2*R*power*S+R*R*s*(
                (2*self.M-2)*integer_power(z,2*self.M-3)*S+power*Sp*2*z/(3*self.z0*self.z0)))
            return residual,derivative
        return implicit_series(r0,sine.prec,equation,2*self.mu*r0.lower())*sine

    def divided_potential(self, a, b):
        """(V(a)-V(b))/(a-b), including a=b, as a real jet in b."""
        difference = a-b
        if not difference[0].contains(0):
            Va = self.potential(arb_series([a], prec=b.prec))
            return (Va-self.potential(b))/difference
        # d_b^k dividedV / k! is an average of V^(k+1)/(k+1)!
        # on the real segment joining a and b. These bounds also apply
        # to boxes meeting flat seams. Only a bound jet is needed here.
        segment = arb(a).union(b[0])
        jet = self.potential(arb_series([segment, 1], prec=b.prec+1))
        delta = arb_series([0]+[b[k] for k in range(1, b.prec)], prec=b.prec)
        result, power = b*0, b*0+1
        for k in range(b.prec):
            result += jet[k+1]*power
            power *= delta
        return result

    def kernel(self, b, phi, zm, right=True):
        si, co = phi.sin(), phi.cos()
        D = zm/(1+si)*self.divided_potential(zm, zm*si)
        if not D[0].is_finite():
            raise ValueError('divided potential interval is not finite')
        lower = self.mu*zm.lower()*zm.lower()
        lo, hi = max(lower.lower(), D[0].lower()), D[0].upper()
        if hi < lo:
            raise ArithmeticError('divided potential contradicts its analytic lower bound')
        D[0] = arb((lo+hi)/2, (hi-lo)/2)
        t = co*D.sqrt()
        speed = zm*self.Xprime(t, 1 if right else self.eta)/(4*D.sqrt())
        return t, arb(1)/2+zm*si/2, speed

    def _cap_integrand(self, b, t, right):
        z = self.root_z_jet(b-t*t)
        S = step_jet((t*t/(self.t0*self.t0)-1)/3)
        r = 1 if right else self.eta
        return (self.sigma-2*r*t)*(1-S)/(2*self.potential_prime(z))

    def quarter_time(self, b, upper, right=True, zm=None, full=False):
        with ctx.workprec(self.bits):
            upper = arb(upper)
            if upper.is_zero():
                return arb(0)
            zm = self.root_z(b) if zm is None else zm
            if b.lower() > (4*self.t0*self.t0).upper():
                # Split X'=2rt+(sigma-2rt)(1-S). The first time
                # integral is r*z/2 exactly; the correction lives only in
                # the tiny central cap. Integrating directly in t avoids
                # the artificial divided-potential cancellation there.
                r = 1 if right else self.eta
                baseline = r*zm*upper.sin()/2
                cap_end = 2*self.t0
                t = arb(0) if full else self.kernel(b, arb_series([upper], prec=1), zm, right)[0][0]
                if t.lower() >= cap_end.upper():
                    return baseline
                if full and self.workers > 1:
                    correction = self._parallel_integral('cap', arb(b), None, cap_end, right)
                elif t.upper() < cap_end.lower():
                    correction = integrate(lambda x: self._cap_integrand(b, x, right), t, cap_end,
                            tolerance=self.tolerance, bits=self.bits, order=self.order, strict_radius=False).value
                else:
                    # The correction is nonnegative below the support end
                    # and identically zero above it. Enclose both branches.
                    value = integrate(lambda x: self._cap_integrand(b, x, right), t.lower(), cap_end,
                            tolerance=self.tolerance, bits=self.bits, order=self.order, strict_radius=False).value
                    correction = arb(0).union(value)
                return baseline+correction
            if self.workers > 1:
                return self._parallel_integral('time', arb(b), zm, upper, right)
            return integrate(lambda phi: self.kernel(b, phi, zm, right)[2], 0, upper,
                             bits=self.bits, tolerance=self.tolerance, order=self.order,
                             strict_radius=False).value

    def _speed_bounds(self, bmin, bmax):
        zmin, zmax = self.root_z(bmin).lower(), self.root_z(bmax).upper()
        # 0<=S'<=8 follows from symmetry and t^m exp(-t) maxima on t>=2.
        Vprime_upper = (2*self.mu*zmax+self.V0*(2*self.M*zmax**(2*self.M-1)
                         +zmax**(2*self.M)*8*2*zmax/(3*self.z0*self.z0))).upper()
        Dmax = (2*Vprime_upper*zmax).upper()
        minX = min(self.sigma.lower(), (2*self.eta*self.t0).lower())
        return (zmin*minX/(4*Dmax.sqrt())).lower()

    def _solve(self, value, derivative, target, guess, lower, lo, hi, radius_goal=None):
        centre = arb(guess).mid()
        radius_goal = arb(self.tolerance)*2**32 if radius_goal is None else arb(radius_goal)
        stagnation = arb(2)**(-self.bits+32)
        for iteration in range(max(512,16*self.bits)):
            residual = value(centre)-target
            root = arb(centre, (abs(residual)/lower).upper())
            if root.rad() < radius_goal or residual.contains(0):
                return root
            try:slope=derivative(centre)
            except (ArithmeticError,ValueError,RuntimeError):slope=lower
            if not slope.is_finite() or not slope > 0:
                slope = lower
            candidate = (centre-residual/slope).mid()
            if residual > 0:
                hi = min(hi, centre)
            elif residual < 0:
                lo = max(lo, centre)
            if not (candidate > lo and candidate < hi) or iteration%8==7:
                candidate = ((lo+hi)/2).mid()
            if abs(candidate-centre) < stagnation:
                return root
            centre = candidate
        raise ArithmeticError('strip scalar inverse did not converge')

    def forward(self, q, p, *, numeric_seed=None,_axis_reflection=False):
        """Return an interval enclosure of the exact nonlinear strip map."""
        with ctx.workprec(self.bits):
            q, p = arb(q), arb(p)
            w = arb.pi()*(q*q+p*p)
            if w.upper() < self.local_w.lower():
                return self.local(q, p)
            if q > 0 and p.contains(0) and not p.is_zero() and not _axis_reflection:
                # Reflect the two angular branches into one closed
                # quadrant. The chart satisfies X(q,-p)=X(q,p),
                # T(q,-p)=1-T(q,p), including its phase-axis limit.
                x,T=self.forward(q,abs(p),numeric_seed=numeric_seed,_axis_reflection=True)
                return x,T.union(1-T)
            if not w > 0:
                raise ValueError('source interval must be refined near the origin')
            # Starting guesses choose trial points only; every root still
            # needs the residual bound and positive derivative lower bound.
            guess = arb(1)
            blo, bhi = arb(guess)/2, arb(guess)*2
            for _ in range(max(64,4*self.bits)):
                if self.area(blo).upper() < w.lower() and self.area(bhi).lower() > w.upper():
                    break
                blo, bhi = blo/2, bhi*2
            else:
                raise ArithmeticError('could not bracket the strip energy')
            speed_lower = self._speed_bounds(blo, bhi)
            period_lower = 2*arb.pi()*speed_lower
            def approximate_period(b):
                z = self.root_z(b)
                return 2*(self.quarter_time(b, arb.pi()/2, True, z, full=True)
                          +self.quarter_time(b, arb.pi()/2, False, z, full=True))
            b = self._solve(self.area, approximate_period, w, guess, period_lower, blo, bhi,
                            radius_goal=arb(self.tolerance)*2**32)
            zm = self.root_z(b)
            Pr = self.quarter_time(b, arb.pi()/2, True, zm, full=True)
            Pl = self.quarter_time(b, arb.pi()/2, False, zm, full=True)
            period = 2*(Pr+Pl)
            if p > 0:
                theta=arb(1)/4-(q/p).atan()/(2*arb.pi())
            elif p < 0:
                theta=arb(3)/4-(q/p).atan()/(2*arb.pi())
            elif q.is_zero():
                theta = arb(1)/4 if p > 0 else arb(3)/4
            elif q > 0:
                theta = (p/q).atan()/(2*arb.pi())
                if p < 0:
                    theta += 1
            elif q < 0:
                theta = arb(1)/2+(p/q).atan()/(2*arb.pi())
            else:
                raise ValueError('refine a source interval spanning an angular branch')
            ratio = Pr/period
            # Uncertain branch comparisons are handled by enclosing both
            # adjacent smooth formulas, never by testing a midpoint.
            cases = []
            if theta.lower() <= ratio.upper():
                cases.append((True, period*theta, 0))
            if theta.upper() >= ratio.lower() and theta.lower() <= arb(1)/2:
                cases.append((False, period*(arb(1)/2-theta), 1))
            if theta.upper() >= arb(1)/2 and theta.lower() <= (1-ratio).upper():
                cases.append((False, period*(theta-arb(1)/2), 2))
            if theta.upper() >= (1-ratio).lower():
                cases.append((True, period*(1-theta), 3))
            points = []
            for right, target, quadrant in cases:
                maximum = Pr if right else Pl
                u0 = min(max((target/maximum).mid()*arb.pi()/2, arb(0)), arb.pi()/2)
                u = self._solve(lambda a: self.quarter_time(b, a, right, zm),
                        lambda a: self.kernel(b, arb_series([a], prec=1), zm, right)[2][0],
                        target, u0, speed_lower, arb(0), arb.pi()/2)
                lo,hi=max(arb(0),u.lower()),min((arb.pi()/2).upper(),u.upper())
                if hi<lo:raise ArithmeticError('strip quadrant inverse misses its analytic domain')
                u=arb((lo+hi)/2,(hi-lo)/2)
                t, T, _ = self.kernel(b, arb_series([u], prec=1), zm, True)
                t, T = t[0], T[0]
                if quadrant in (1, 2):
                    t = -t
                if quadrant in (2, 3):
                    T = 1-T
                if abs(t).upper() <= self.t0:
                    x = self.c+self.sigma*t
                elif t > 0:
                    x = self.c+self.F(t)
                elif t < 0:
                    x = self.c-self.F(-t, self.eta)
                else:
                    raise ValueError('refine final X interval across its central collar')
                points.append((x, T))
            x, y = points[0]
            for next_x, next_y in points[1:]:
                x, y = x.union(next_x), y.union(next_y)
            return x, y
