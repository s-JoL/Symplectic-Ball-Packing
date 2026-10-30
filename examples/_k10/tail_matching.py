"""A common Hamiltonian using a nearby exact symplectic linear frame.

The nonlinear shape stage is identically zero. At the start of the tail,
the affine balls already lie in the reference tail charts, by the
certified contraction ||A_i^-1 Df_i-I||<=eta_i. The tail therefore uses
different, explicitly computed source labels. Its time-one images lie
in f_i(B(r1)), which is enough for the packing.
"""
from flint import arb,ctx
from .hamiltonian_core import CommonHamiltonian,mv,norm
from .arb_cache import ball_key


class TailMatching:
    def enable_tail_matching(self,bounds):
        with ctx.workprec(self.bits):
            if len(bounds)!=self.k:raise ValueError('one local frame-variation bound is required per ball')
            self.frame_variation=[arb(x).upper() for x in bounds]
            limit=((self.r1-1)/(2*self.r1)).lower()
            if not all(x>=0 and x<limit for x in self.frame_variation):
                raise ValueError('refine the local differential enclosures to match the tail plateau')
            self._tail_labels={}

    def _label_point(self,u,i):
        target=[y+self.tau*x for y,x in zip(self.centres[i],mv(self.paths[i].A,u))]
        source=self.embeddings[i].preimage(target)
        if source is None:raise ArithmeticError('a certified interior tail label was excluded')
        return [x/self.tau for x in source]

    def matching_label(self,u,i):
        with ctx.workprec(self.bits):
            u=list(map(arb,u))
            if all(x.is_zero() for x in u):return [arb(0)]*4
            if norm(u).upper()>self.r1.lower()*(1-self.frame_variation[i]):
                raise ValueError('source point is outside the certified tail plateau')
            key=i,tuple(ball_key(x) for x in u),self.bits
            if key not in self._tail_labels:
                label=self._label_point(u,i)
                if not norm(label).upper()<self.r1.lower():
                    raise ArithmeticError('tail label enclosure needs greater precision')
                self._tail_labels[key]=label
            return self._tail_labels[key]

    def source_generator(self,t,u,i):
        with ctx.workprec(self.bits):
            stage,_,speed=self.clock(arb(t))
            if stage==6 or speed.is_zero():return arb(0)
            if stage==7:u=self.matching_label(u,i)
            return super().source_generator(t,u,i)

    def generator_on_chart(self,t,u,i):
        with ctx.workprec(self.bits):
            stage,_,speed=self.clock(arb(t))
            if stage==6 or speed.is_zero():return arb(0)
            # The ambient inverse has already returned a tail-chart
            # coordinate. It must not be relabelled a second time.
            return super().source_generator(t,u,i)

    def isotopy(self,t,u,i):
        with ctx.workprec(self.bits):
            t,u=arb(t),list(map(arb,u))
            if t>=1:return list(self.embeddings[i].value(self.matching_label(u,i)))
            if t<=0:return super().isotopy(t,u,i)
            stage,sigma,_=self.clock(t)
            if stage==6:return [y+x for y,x in zip(self.far[i],mv(self.paths[i].A,u))]
            if stage==7:
                if sigma.is_zero():
                    return [y+x for y,x in zip(self.far[i],mv(self.paths[i].A,u))]
                v=self.tau+(1-self.tau)*sigma
                label=self.matching_label(u,i)
                return [x/v for x in self.embeddings[i].value([v*x for x in label])]
            return super().isotopy(t,u,i)

    def value(self,t,y):
        with ctx.workprec(self.bits):
            stage,_,speed=self.clock(arb(t))
            if stage==6 or speed.is_zero():return arb(0)
            return super().value(t,y)


class TailHamiltonian(TailMatching,CommonHamiltonian):
    def __init__(self,embeddings,local_derivative_bounds,local_radius,target_radius,
                 frame_variation,*,bits=256,frozen=None):
        super().__init__(embeddings,local_derivative_bounds,local_radius,target_radius,bits=bits,frozen=frozen)
        self.enable_tail_matching(frame_variation)
