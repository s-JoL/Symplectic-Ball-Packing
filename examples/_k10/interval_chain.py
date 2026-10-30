"""End-to-end interval evaluation of the real k10 embedding formulas.

Numerical objects supply root starting guesses only. A result is accepted
only if its final Arb coordinate radii satisfy the requested accuracy.
Unresolved interval branch decisions fail explicitly; no midpoint decision
is accepted as a mathematical certificate.
"""
import math
from .arb_cache import floor_mid,nearest_mid,root_precision

from flint import arb, arb_series, ctx
from .interval_bump import step_jet
from .interval_strip import IntervalStrip
from .verified_moser import base_geometry, suspension
from .verified_normal import normal_to_ball
from .direct_cubic_bridge import DirectCubicBridge


class IntervalK10:
    def __init__(self, numeric, bits=384, tolerance='1e-60', progress=None, quad_workers=16):
        self.numeric, self.bits, self.tolerance, self.progress = numeric, bits, tolerance, progress
        self.P, self.data = numeric.parameters, numeric.path.data
        with ctx.workprec(bits):
            self.pi, self.e = arb.pi(), arb(self.P.e)
            self.a, self.smoothing = arb(self.P.a), arb(self.P.smoothing)
            self.c = arb(self.P.c)
            self.strip = IntervalStrip(self.P.rho, self.P.strip_delta, bits, tolerance, workers=quad_workers)

    @staticmethod
    def step(x, derivative=0):
        return step_jet(arb_series([x], prec=1), derivative)[0]

    def base(self, v):
        B, b = base_geometry(arb_series([v], prec=1))
        return B[0], b[0]

    def clock(self, u):
        n = floor_mid(u)
        t = u-n
        if not (t.lower() >= 0 and t.upper() <= 1):
            raise ArithmeticError('refine a clock interval crossing an integer seam')
        return n, self.step((t-arb(.4))/arb(.2))

    def global_clock(self, u):
        nearest = nearest_mid(u)
        if abs(u-nearest).upper() < arb('.3'):
            return arb(nearest)
        n, F = self.clock(u)
        return n+F

    def I(self, z):
        return self.pi*(z[0]*z[0]+z[1]*z[1])

    def rotate(self, z, turns):
        angle = 2*self.pi*turns
        c, s = angle.cos(), angle.sin()
        return [c*z[0]-s*z[1], s*z[0]+c*z[1]]

    def path(self, z, t):
        c = arb(self.data['center'])
        w = [z[0]-c, z[1]]
        r2 = w[0]*w[0]+w[1]*w[1]
        inner, outer = arb(self.data['rin']**2), arb(self.data['rout']**2)
        argument = (r2-inner)/(outer-inner)
        chi, chip = 1-self.step(argument), -self.step(argument, 1)
        speed = self.pi*(chi+(r2-outer)*chip/(outer-inner))
        rotated = self.rotate(w, t*speed/(2*self.pi))
        return [rotated[0]+c, rotated[1]]

    def path_action(self,z,t):
        c=arb(self.data['center'])
        r2=(z[0]-c)*(z[0]-c)+z[1]*z[1]
        inner,outer=arb(self.data['rin']**2),arb(self.data['rout']**2)
        argument=(r2-inner)/(outer-inner)
        chi,chip=1-self.step(argument),-self.step(argument,1)
        speed=self.pi*(chi+(r2-outer)*chip/(outer-inner))
        Q=self.pi/2*(r2-outer)*chi
        mapped=self.path(z,t)
        return t*(speed*r2/2-Q)+c*(mapped[1]-z[1])/2

    def initial_base_exact(self,state):
        u,v=state[:2]
        B,_=self.base(v)
        return (3-self.e)*u*(v-B)

    def hi(self, p):
        d = self.a-p
        return (d+(d*d+self.smoothing*self.smoothing).sqrt())/2

    def hip(self, p):
        d = self.a-p
        return -(1+d/(d*d+self.smoothing*self.smoothing).sqrt())/2

    def H(self, p):
        return 3-9*p-self.e

    def root(self, value_derivative, guess, lo, hi):
        centre = arb(guess).mid()
        lo, hi = arb(lo), arb(hi)
        if not centre.is_finite() or not lo<=centre<=hi:centre=((lo+hi)/2).mid()
        for iteration in range(max(512,16*self.bits)):
            residual, derivative = value_derivative(centre)
            result = arb(centre, (abs(residual)/self.e).upper())
            # The global e-bound first encloses the root. A derivative
            # bound on that enclosure can then sharpen it by the mean
            # value theorem, including genuine parameter boxes.
            for _ in range(4):
                try:
                    _,slope=value_derivative(result)
                    lower=max(self.e,slope.lower())
                    radius=(abs(residual)/lower).upper()
                    if not radius<result.rad():break
                    result=arb(centre,radius)
                except (ArithmeticError,ValueError,ZeroDivisionError):
                    break
            if residual.contains(0):
                return result
            if residual > 0:
                hi = min(hi, centre)
            elif residual < 0:
                lo = max(lo, centre)
            if not derivative > 0:
                derivative = self.e
            next_centre = (centre-residual/derivative).mid()
            if not (next_centre > lo and next_centre < hi) or iteration%8==7:
                next_centre = ((lo+hi)/2).mid()
            if abs(next_centre-centre) < arb(self.tolerance)/2**16:
                return result
            centre = next_centre
        raise ArithmeticError('flat scalar root did not converge')

    def ball_layer(self, source, index, *, with_action=False):
        x, T = self.strip.forward(source[1], source[3])
        p = self.I([source[0], source[2]])
        hi, hip = self.hi(p), self.hip(p)
        start = arb(self.numeric.model.ball_layer.starts[index])
        width = arb(self.numeric.model.ball_layer.width)
        seed = [start+width/2, arb('1/2')]
        def equation_u(u):
            ramp = self.step((u-start)/width)
            ramp_prime = self.step((u-start)/width, 1)/width
            return self.e*(u-start)+ramp*hi-x, self.e+ramp_prime*hi
        u = self.root(equation_u, seed[0], start, start+width)
        ramp = self.step((u-start)/width)
        A = self.step((u-start)/width, 1)/width*hi
        def equation_v(v):
            B, b = self.base(v)
            return self.e*v+A*B-(self.e+A)*T, self.e+A*b
        v = self.root(equation_v, seed[1], 0, 1)
        B, _ = self.base(v)
        C = ramp*hip*(B-T)+(arb(3*math.sqrt(10))+index*hip)*B
        z = self.rotate([source[0], source[2]], -C)
        n, F = self.clock(u)
        z = self.path(z, -(n+F))
        if with_action:
            _,strip_action=self.strip.inverse(x,T,with_action=True)
            ai=arb(3*math.sqrt(10))*p-3+self.e+index*hi
            generating=self.e*(u-start)*(v-T)+ramp*hi*(B-T)+ai*B+self.e*start*v
            action=strip_action+generating-p*C-self.path_action(z,n+F)
            action+=(3-self.e)*u*(v-B)
        z = self.rotate(z, 9*u*(v-B))
        result=[u,v,*z]
        return (result,action) if with_action else result

    def local_fibre(self, state, cell=None):
        u, v, *z = state
        n = floor_mid(u) if cell is None else cell
        B, _ = self.base(v)
        return self.rotate(z, -9*u*(v-B)-n*(9*B+arb(3)/2))

    def from_local(self, u, v, z, cell):
        B, _ = self.base(v)
        return [u, v, *self.rotate(z, 9*u*(v-B)+cell*(9*B+arb(3)/2))]

    def layer_inverse(self, state, *, with_action=False):
        return self.layer_map(state,inverse=True,with_action=with_action)

    def layer_forward(self,state,*,with_action=False):
        return self.layer_map(state,inverse=False,with_action=with_action)

    def layer_map(self,state,*,inverse=False,with_action=False,_cell=None):
        # Use both developed charts when an input enclosure crosses a
        # lattice seam. Choosing floor(midpoint) alone cannot enclose the
        # whole source box. Each closed half has a valid clock chart.
        u=state[0];value=u.value if hasattr(u,'gradient') else u
        seam_index=nearest_mid(value);seam=arb(seam_index)
        if _cell is None and value.lower()<seam<value.upper():
            if value.rad()>=arb(1)/2:raise ArithmeticError('subdivide a layer input spanning several lattice cells')
            pieces=[]
            for lo,hi,cell in [(value.lower(),seam,seam_index-1),(seam,value.upper(),seam_index)]:
                piece=arb((lo+hi)/2,(hi-lo)/2)
                if hasattr(u,'gradient'):piece=type(u)(piece,u.gradient)
                pieces.append(self.layer_map([piece,*state[1:]],inverse=inverse,with_action=with_action,_cell=cell))
            if with_action:
                return [a.union(b) for a,b in zip(pieces[0][0],pieces[1][0])],pieces[0][1].union(pieces[1][1])
            return [a.union(b) for a,b in zip(*pieces)]
        lam0,lam1=(1,0) if inverse else (0,1)
        u, v, *_ = state
        if _cell is None:cell,F=self.clock(u)
        else:cell,F=_cell,self.step((u-_cell-arb(.4))/arb(.2))
        B, b = self.base(v)
        if b.is_zero():
            return (state,arb(0)) if with_action else state
        z = self.local_fibre(state, cell)
        w = self.path(z, F)
        p = self.I(w)
        J, hi = (self.c+9)*p-3+self.e, self.hi(p)
        residual = self.c*self.I(self.path(w, -1))-J-10*hi
        total = sum(self.step((u-cell-arb(.4+(j+.12)*(.2/11)))/arb(.76*(.2/11))) for j in range(10))
        reserve = self.step((u-cell-arb(.4+(10+.12)*(.2/11)))/arb(.76*(.2/11)))
        value = self.e*u+b*((1-lam0)*F*self.H(self.I(self.path(w,-1)))+lam0*(J+total*hi+reserve*residual))
        qin=self.path_action(z,F) if with_action else arb(0)
        pending = [(cell, w, arb(0), 0, 0, arb(0))]
        candidates = []
        while pending:
            cell, w, offset, direction, crossed, qoffset = pending.pop()
            if crossed > self.numeric.model.cell_search_bound():
                raise ArithmeticError('layer cell search exceeded its proved bound')
            qm = self.path(w, -1)
            Jw=(self.c+9)*self.I(w)-3+self.e
            lo = self.e*cell+b*(lam1*Jw+offset)
            Jqm=(self.c+9)*self.I(qm)-3+self.e
            upper = self.e*(cell+1)+b*(self.H(self.I(qm))+lam1*Jqm+offset)
            if value.lower() <= upper.upper() and value.upper() >= lo.lower():
                candidates.append((cell, w, offset,qoffset))
            if direction <= 0 and value.lower() < lo.upper():
                previous = self.path(self.rotate(w, 9*B+arb(3)/2), 1)
                next_qoffset=qoffset-self.path_action(self.rotate(w,9*B+arb(3)/2),1) if with_action else arb(0)
                pending.append((cell-1, previous, offset-self.H(self.I(w)), -1, crossed+1,next_qoffset))
            if direction >= 0 and value.upper() > upper.lower():
                following = self.rotate(qm, -9*B-arb(3)/2)
                next_qoffset=qoffset+self.path_action(qm,1) if with_action else arb(0)
                pending.append((cell+1, following, offset+self.H(self.I(following)), 1, crossed+1,next_qoffset))
        results = [];actions=[]
        for cell, w, offset,qoffset in candidates:
            hm = self.H(self.I(self.path(w, -1)))
            p=self.I(w);Jw=(self.c+9)*p-3+self.e;hip=self.hi(p)
            resw=self.c*self.I(self.path(w,-1))-Jw-10*hip
            def equation(t):
                F = self.step((t-arb(.4))/arb(.2))
                Fp = self.step((t-arb(.4))/arb(.2), 1)/arb(.2)
                total=sum(self.step((t-arb(.4+(j+.12)*(.2/11)))/arb(.76*(.2/11))) for j in range(10))
                totalp=sum(self.step((t-arb(.4+(j+.12)*(.2/11)))/arb(.76*(.2/11)),1)/arb(.76*(.2/11)) for j in range(10))
                reserve=self.step((t-arb(.4+(10+.12)*(.2/11)))/arb(.76*(.2/11)))
                reservep=self.step((t-arb(.4+(10+.12)*(.2/11)))/arb(.76*(.2/11)),1)/arb(.76*(.2/11))
                G=(1-lam1)*F*hm+lam1*(Jw+total*hip+reserve*resw)
                Gu=(1-lam1)*Fp*hm+lam1*(totalp*hip+reservep*resw)
                return self.e*(cell+t)+b*(G+offset)-value,self.e+b*Gu
            t = self.root(equation, arb(1)/2, 0, 1)
            F = self.step((t-arb(.4))/arb(.2))
            zout=self.path(w,-F)
            result=self.from_local(cell+t,v,zout,cell)
            results.append(result)
            if with_action:
                actions.append(self.initial_base_exact(result)-self.initial_base_exact(state)
                               -self.path_action(zout,F)+qin-qoffset)
        if not results:
            raise ArithmeticError('no layer cell contains the target value')
        result = results[0]
        for candidate in results[1:]:
            result = [a.union(b) for a, b in zip(result, candidate)]
        if not with_action:return result
        action=actions[0]
        for value in actions[1:]:action=action.union(value)
        return result,action

    def base_inverse(self, state, *, with_action=False):
        U, V, *z = state
        p = self.I(z)
        m, H = 3-9*p, self.H(p)
        B, b = self.base(V)
        f = self.global_clock(U)
        v = V+H/m*(B-V)
        u = U+H*b/(self.e+H*b)*(f-U)
        A, C = 9*u*(B-v), U*(V-B)
        result=[u,v,*self.rotate(z,-A-9*C)]
        return (result,-p*A-(3-self.e)*C) if with_action else result

    def shear_inverse(self, state):
        u, v, *z = state
        B, b = self.base(v)
        p = self.I(z)
        return [u-arb(1)/2*p/(3-9*p)*b, v, *self.rotate(z, B/2)]

    def shear_forward(self,state):
        u,v,*z=state
        B,b=self.base(v);p=self.I(z)
        return [u+arb(1)/2*p/(3-9*p)*b,v,*self.rotate(z,-B/2)]

    def base_forward(self,state):
        u,v,*z=state;p=self.I(z);m,H=3-9*p,self.H(p)
        nv=floor_mid(v)
        def equation_v(V):
            B,b=self.base(V)
            return self.e*V+H*B-m*v,self.e+H*b
        V=self.root(equation_v,v,nv,nv+1)
        B,b=self.base(V);nu=floor_mid(u)
        def equation_u(U):
            nearest=nearest_mid(U)
            if abs(U-nearest).upper()<arb('.3'):
                clock,Fp=arb(nearest),arb(0)
            else:
                n,F=self.clock(U)
                clock=n+F
                Fp=self.step((U-n-arb(.4))/arb(.2),1)/arb(.2)
            return self.e*U+H*b*clock-(self.e+H*b)*u,self.e+H*b*Fp
        U=self.root(equation_u,u,nu,nu+1)
        A,C=9*u*(B-v),U*(V-B)
        return [U,V,*self.rotate(z,A+9*C)]

    def ball_layer_inverse(self,state,index):
        u,v,*z=state
        B,_=self.base(v)
        z=self.rotate(z,-9*u*(v-B))
        n,F=self.clock(u);w=self.path(z,n+F);p=self.I(w)
        start=arb(self.numeric.model.ball_layer.starts[index]);width=arb(self.numeric.model.ball_layer.width)
        ramp=self.step((u-start)/width)
        A=self.step((u-start)/width,1)/width*self.hi(p)
        x=self.e*(u-start)+ramp*self.hi(p)
        T=B+self.e/(self.e+A)*(v-B)
        C=ramp*self.hip(p)*(B-T)+(arb(3*math.sqrt(10))+index*self.hip(p))*B
        q2,p2=self.strip.inverse(x,T)
        q1,p1=self.rotate(w,C)
        return [q1,q2,p1,p2]

    def forward(self, original, index, accuracy='1e-8', neighbourhood=False,range_only=False,
                flow_order=None,guard_bits=None,local_moser=False):
        if not 0 <= index < 10 or len(original) != 4:
            raise ValueError('expected a four-dimensional point and ball index 0..9')
        with ctx.workprec(self.bits):
            local = [arb(v)-(3*index if j == 0 else 0) for j, v in enumerate(original)]
            if neighbourhood:
                m = self.strip.mu/3+self.strip.V0/(2*self.strip.M+1)
                rho_bar = (arb(self.P.rho)+min(arb(self.P.rho)+(self.strip.delta-m)/2,
                            self.a-self.strip.delta))/2
                if not self.pi*arb(self.numeric.sigma)*arb(self.numeric.sigma)*sum(x*x for x in local) < rho_bar:
                    raise ValueError('point is not certified in the open source neighbourhood')
            elif sum(x*x for x in local).upper() > 1:
                raise ValueError('point is not certified in its closed source unit ball')
            source = [arb(self.numeric.sigma)*x for x in local]
            state = self.ball_layer(source, index)
            if self.progress: self.progress('ball_layer', state)
            state = self.layer_inverse(state)
            if self.progress: self.progress('layer', state)
            flow_order = max(24, self.bits//16) if flow_order is None else flow_order
            guard_bits = 128+max(0, (self.bits-384)//2) if guard_bits is None else guard_bits
            flow = suspension(state, self.P, self.data, inverse=True,local_frame=local_moser,bits=self.bits, order=flow_order,
                              max_step='.0078125', max_radius=accuracy, remainder_guard_bits=guard_bits,
                              max_steps=max(100000, self.bits**3),
                              progress=None if self.progress is None else lambda info:self.progress('suspension_flow',info))
            state = self.shear_inverse(self.base_inverse(flow.endpoint))
            if self.progress: self.progress('landau', state)
            bridge = DirectCubicBridge(bits=self.bits, root_bits=root_precision(self.bits,accuracy), workers=1)
            initial, _ = bridge.old_normal_input(*state, arb(self.P.d))
            point, diagnostics = normal_to_ball(initial, arb(self.P.d), bits=self.bits, order=flow_order,
                                                max_radius=accuracy, max_step='.0078125', remainder_guard_bits=guard_bits,
                                                max_steps=max(100000, self.bits**3),
                                                progress=None if self.progress is None else lambda info:self.progress('normal_flow',info))
            result = tuple(x/arb(self.numeric.sigma) for x in point)
            if not range_only and max(x.rad() for x in result) > arb(accuracy):
                raise ArithmeticError('final embedding enclosure is wider than requested')
            if not range_only and not sum(x*x for x in result) < arb(73)/40*arb(73)/40:
                raise ArithmeticError('target-ball inclusion was not certified')
            return result, diagnostics
