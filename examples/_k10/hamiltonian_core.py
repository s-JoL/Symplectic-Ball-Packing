"""Common eight-stage ambient Hamiltonian from exact embedding oracles.

Convention: i_X omega=dH, X=(H_p,-H_q), as in paper/main/hamiltonian.tex.
An embedding oracle must supply its value, a normalized primitive S with
dS=f*lambda-lambda, its exact symplectic derivative at zero, and a certified
preimage operation. TailMatching permits a nearby exact symplectic frame
under its additional uniform differential contract. Actual K10 adapters
live in k10_hamiltonian_adapter.py.
"""
from dataclasses import dataclass

from flint import arb, arb_mat, arb_series, ctx
from .interval_bump import step_jet


def omega(x, y):
    return sum(x[j]*y[j+2]-x[j+2]*y[j] for j in range(2))


def dot(x, y):
    return sum(a*b for a, b in zip(x, y))


def norm(x):
    # Generic interval products can have a negative lower endpoint when
    # the same zero-containing variable is multiplied by itself.
    lower=sum((arb(0) if a.contains(0) else min(abs(a.lower()),abs(a.upper())))**2 for a in x)
    upper=sum(abs(a).upper()*abs(a).upper() for a in x)
    return max(arb(0),lower.lower()).sqrt().lower().union(upper.upper().sqrt().upper())


def identity(n=4):
    return arb_mat([[int(i == j) for j in range(n)] for i in range(n)])


def mv(A, x):
    result = A*arb_mat([[v] for v in x])
    return [result[j, 0] for j in range(A.nrows())]


def block(A, r, c, n=2):
    return arb_mat([[A[r+i, c+j] for j in range(n)] for i in range(n)])


def blocks(a, b, c, d):
    return arb_mat([[a[i, j] if i < 2 and j < 2 else b[i, j-2] if i < 2 else
                     c[i-2, j] if j < 2 else d[i-2, j-2] for j in range(4)] for i in range(4)])


def ceil_positive(x):
    m, e = x.upper().man_exp()
    m, e = int(m), int(e)
    if m < 0:
        raise ValueError('expected a positive bound')
    if e >= 0:
        return m << e
    shift = -e
    return 1 if shift > m.bit_length() else (m+(1 << shift)-1) >> shift


def dyadic_below(x):
    if not x > 0:
        raise ArithmeticError('a positive separation/scale bound is required')
    m, e = x.lower().man_exp()
    exponent = int(m).bit_length()-1+int(e)
    result = arb((1, exponent))
    return result if result <= x.lower() else arb((1, exponent-1))


class SymplecticPath:
    """The paper's polar/shear/Cayley path for a certified exact Sp(4) input."""
    def __init__(self, A, angle_index=None):
        self.A = arb_mat(A)
        A = self.A
        I, Z = identity(2), arb_mat([[0, 0], [0, 0]])
        self.Jc = blocks(Z, -I, I, Z)
        a, c = block(A, 0, 0), block(A, 2, 0)
        G = a.transpose()*a+c.transpose()*c
        determinant_root = G.det().sqrt()
        self.P = (G+determinant_root*I)/(G[0, 0]+G[1, 1]+2*determinant_root).sqrt()
        Pinv = self.P.inv()
        ahat, chat = a*Pinv, c*Pinv
        U = blocks(ahat, -chat, chat, ahat)
        self.T = Pinv*block(U.transpose()*A, 0, 2)
        choices = range(3) if angle_index is None else [angle_index]
        for m in choices:
            theta = arb.pi()*m/3
            V = self.rotation(theta)*U
            if not (V+identity()).det().contains(0):
                self.angle_index, self.theta = m, theta
                self.X = (V-identity())*(V+identity()).inv()
                break
        else:
            raise ArithmeticError('increase precision to certify a Cayley angle')
        frobenius = lambda M: sum(abs(M[i, j]).upper()*abs(M[i, j]).upper() for i in range(M.nrows())
                                  for j in range(M.ncols())).sqrt().upper()
        self.norm_bound = max(arb(1), frobenius(self.P).upper(), frobenius(Pinv).upper())*(1+frobenius(self.T).upper())

    def rotation(self, theta):
        return theta.cos()*identity()+theta.sin()*self.Jc

    def evaluate(self, sigma):
        I, I2, Z = identity(), identity(2), arb_mat([[0, 0], [0, 0]])
        beta = (arb.pi()*sigma/2).sin()
        beta_prime = arb.pi()/2*(arb.pi()*sigma).sin()
        P = I2+beta*beta*(self.P-I2)
        Pdot = beta_prime*(self.P-I2)
        Pinv = P.inv()
        R = self.rotation(-sigma*self.theta)
        Rdot = -self.theta*self.Jc*R
        inverse = (I-sigma*self.X).inv()
        C = (I+sigma*self.X)*inverse
        Cdot = (I+C)*self.X*inverse
        D, Ddot = blocks(P, Z, Z, Pinv), blocks(Pdot, Z, Z, -Pinv*Pdot*Pinv)
        U, Udot = blocks(I2, sigma*self.T, Z, I2), blocks(Z, self.T, Z, Z)
        M = R*C*D*U
        Mdot = Rdot*C*D*U+R*Cdot*D*U+R*C*Ddot*U+R*C*D*Udot
        return M, Mdot


@dataclass
class ExactEmbedding:
    value: object
    action: object
    linear: object
    preimage: object


class CommonHamiltonian:
    """Conditional on the certified oracle contracts stated above.

    local_derivative_bounds bound ||Df_i|| on a round source neighbourhood
    of radius local_radius. They need not bound the whole source ball.
    Embeddings must extend to r4, have disjoint images on r3, and lie in
    target_radius there. The constructor's constants are frozen once.
    """
    def __init__(self, embeddings, local_derivative_bounds, local_radius,
                 target_radius, bits=256, frozen=None):
        self.embeddings, self.bits = embeddings, bits
        with ctx.workprec(bits):
            self.k = len(embeddings)
            if not self.k:
                raise ValueError('at least one embedding oracle is required')
            self.r1, self.r2 = arb('20001/20000'), arb('10001/10000')
            self.r3, self.r4 = arb('20003/20000'), arb('5001/5000')
            self.sources = [[arb(3*i), arb(0), arb(0), arb(0)] for i in range(self.k)]
            self.centres = [list(f.value([arb(0)]*4)) for f in embeddings]
            self.paths = [SymplecticPath(f.linear(),None if frozen is None else frozen['angles'][i])
                          for i,f in enumerate(embeddings)]
            if len(local_derivative_bounds) != self.k:
                raise ValueError('one certified derivative bound is required for each ball')
            self.derivative_bounds=list(map(arb,local_derivative_bounds))
            if not arb(local_radius) > 0 or not arb(target_radius) > 0:
                raise ValueError('positive local and target radii are required')
            L = 1+sum(arb(D)+self.r3*p.norm_bound for D, p in zip(local_derivative_bounds, self.paths))
            self.L = arb(ceil_positive(L) if frozen is None else frozen['L'])
            if not self.L>=L.upper():raise ValueError('frozen linear radius bound is insufficient')
            rtotal = 1+self.k*self.r3
            separation = (min(norm([a-b for a, b in zip(self.centres[i], self.centres[j])]).lower()
                           for i in range(self.k) for j in range(i)))/2 if self.k > 1 else arb(1)
            self.delta = dyadic_below(separation) if frozen is None else arb(frozen['delta'])
            if not 0<self.delta<=separation.lower():raise ValueError('frozen separation bound is insufficient')
            tau_bound=min(x.lower() for x in
                [arb(1)/2, self.delta/(2*self.L*rtotal), arb(local_radius)/self.r3])
            self.tau = dyadic_below(tau_bound) if frozen is None else arb(frozen['tau'])
            if not 0<self.tau<=tau_bound:raise ValueError('frozen matching scale is too large')
            self.far = [[x/self.tau for x in y] for y in self.centres]
            # Any orthonormal pair works for the translation route. A
            # generic polynomial direction avoids undecidable rank ties.
            choices=range(1,3*self.k*(self.k-1)//2+2) if frozen is None else [frozen['direction_index']]
            for m in choices:
                v = list(map(arb, [1, m, m*m, m*m*m]))
                v = [x/norm(v) for x in v]
                projection = [dot(y, v) for y in self.centres]
                if all(not (projection[i]-projection[j]).contains(0) for i in range(self.k) for j in range(i)):
                    self.direction_index, self.dirP = m, v
                    order = sorted(range(self.k), key=lambda i: projection[i].mid())
                    self.ranksP = [order.index(i) for i in range(self.k)]
                    if frozen is not None and self.ranksP!=frozen['ranksP']:
                        raise ValueError('the frozen route ranks disagree with the centre enclosures')
                    break
            else:
                raise ArithmeticError('increase centre precision to certify route ranks')
            q = [arb(int(j == 0))-self.dirP[0]*self.dirP[j] for j in range(4)]
            qnorm = norm(q)
            self.dirQ = [x/qnorm for x in q]
            route_bound=1+sum(2*(self.r3+norm(s)+norm(y)) for s,y in zip(self.sources,self.far))
            self.route_scale = arb(ceil_positive(route_bound) if frozen is None else frozen['route_scale'])
            if not self.route_scale>=route_bound.upper():raise ValueError('frozen route scale is insufficient')
            support_bound=2*self.k*self.route_scale+self.L*rtotal+arb(target_radius)/self.tau
            self.support_radius = arb(ceil_positive(support_bound) if frozen is None else frozen['support_radius'])
            if not self.support_radius>=support_bound.upper():raise ValueError('frozen support radius is insufficient')

    def configuration(self):
        """Exact discrete/rational choices; refining precision keeps the same H."""
        from flint import fmpq
        def exact(x):
            m,e=x.mid().man_exp();m,e=int(m),int(e)
            return str(fmpq(m<<e) if e>=0 else fmpq(m,1<<(-e)))
        return dict(angles=[p.angle_index for p in self.paths],L=exact(self.L),delta=exact(self.delta),
                    tau=exact(self.tau),direction_index=self.direction_index,ranksP=self.ranksP,
                    route_scale=exact(self.route_scale),support_radius=exact(self.support_radius))

    @staticmethod
    def step(t, derivative=0):
        return step_jet(arb_series([t], prec=1), derivative)[0]

    def clock(self, t):
        if t <= 0 or t >= 1:
            return None, arb(0), arb(0)
        m = int((8*t.mid()).floor().unique_fmpz())
        if (8*t).lower() < m or (8*t).upper() > m+1:
            raise ArithmeticError('subdivide a time interval at the isotopy stage boundary')
        return m, self.step(8*t-m), 8*self.step(8*t-m, 1)

    def route(self, t, i):
        s, Y = self.sources[i], self.far[i]
        clocks = [self.step(8*t-j) for j in range(5)]
        return [s[j]+clocks[2]*(Y[j]-s[j])+self.route_scale*(clocks[0]-clocks[3])*i*self.dirQ[j]
                +self.route_scale*(clocks[1]-clocks[4])*self.ranksP[i]*self.dirP[j] for j in range(4)]

    def isotopy(self, t, u, i):
        with ctx.workprec(self.bits):
            t, u = arb(t), list(map(arb, u))
            if t <= 0:
                return [a+b for a, b in zip(self.sources[i], u)]
            if t >= 1:
                return list(self.embeddings[i].value(u))
            stage, sigma, _ = self.clock(t)
            if stage <= 4:
                return [a+b for a, b in zip(self.route(t, i), u)]
            if stage == 5:
                M, _ = self.paths[i].evaluate(sigma)
                return [a+b for a, b in zip(self.far[i], mv(M, u))]
            if stage == 6:
                rho = self.tau*sigma
                if rho.is_zero():
                    return [a+b for a, b in zip(self.far[i], mv(self.paths[i].A, u))]
                f = self.embeddings[i].value([rho*x for x in u])
                return [Y+(x-y)/rho for Y, x, y in zip(self.far[i], f, self.centres[i])]
            v = self.tau+(1-self.tau)*sigma
            return [x/v for x in self.embeddings[i].value([v*x for x in u])]

    def source_generator(self, t, u, i):
        with ctx.workprec(self.bits):
            t, u = arb(t), list(map(arb, u))
            stage, sigma, speed = self.clock(t)
            if stage is None or speed.is_zero():
                return arb(0)
            if stage <= 4:
                if stage in (0, 3):
                    w = [self.route_scale*i*x*(1 if stage == 0 else -1) for x in self.dirQ]
                elif stage in (1, 4):
                    w = [self.route_scale*self.ranksP[i]*x*(1 if stage == 1 else -1) for x in self.dirP]
                else:
                    w = [a-b for a, b in zip(self.far[i], self.sources[i])]
                return speed*omega(w, u)
            if stage == 5:
                M, Mdot = self.paths[i].evaluate(sigma)
                return speed*omega(mv(Mdot, u), mv(M, u))/2
            if stage == 6:
                rho = self.tau*sigma
                x = [rho*v for v in u]
                centred_action = self.embeddings[i].action(x)-omega(self.centres[i], self.embeddings[i].value(x))/2
                return -2*self.tau*speed*centred_action/(rho*rho*rho)
            v = self.tau+(1-self.tau)*sigma
            return -2*(1-self.tau)*speed*self.embeddings[i].action([v*x for x in u])/(v*v*v)

    def generator_on_chart(self,t,u,i):
        return self.source_generator(t,u,i)

    def value(self, t, y):
        with ctx.workprec(self.bits):
            t, y = arb(t), list(map(arb, y))
            stage, sigma, speed = self.clock(t)
            if stage is None or speed.is_zero() or norm(y).lower() > self.support_radius:
                return arb(0)
            result = arb(0)
            for i, f in enumerate(self.embeddings):
                if stage <= 4:
                    u = [a-b for a, b in zip(y, self.route(t, i))]
                elif stage == 5:
                    M, _ = self.paths[i].evaluate(sigma)
                    u = mv(M.inv(), [a-b for a, b in zip(y, self.far[i])])
                elif stage == 6:
                    if norm([a-b for a,b in zip(y,self.far[i])]).lower()>(self.derivative_bounds[i]*self.r2).upper():
                        continue
                    rho = self.tau*sigma
                    z = f.preimage([rho*a+(1-sigma)*c for a,c in zip(y,self.centres[i])])
                    u = None if z is None else [x/rho for x in z]
                else:
                    v = self.tau+(1-self.tau)*sigma
                    z = f.preimage([v*x for x in y])
                    u = None if z is None else [x/v for x in z]
                if u is None:
                    continue
                r2 = dot(u, u)
                if r2.lower() >= (self.r2*self.r2).upper():
                    continue
                if r2.upper() >= (self.r3*self.r3).lower():
                    raise ArithmeticError('refine the preimage across the cutoff collar')
                cutoff = 1-self.step((r2-self.r1*self.r1)/(self.r2*self.r2-self.r1*self.r1))
                result += cutoff*self.generator_on_chart(t, u, i)
            if not result.is_finite():
                raise ArithmeticError('increase oracle precision for the Hamiltonian enclosure')
            return result
