"""Validated reverse chain for actual K10 image points.

Only explicit domain exclusions return None. An unresolved numerical or
interval calculation raises an error; it is never called 'no preimage'.
"""
import math
from .arb_cache import floor_mid,nearest_mid,root_precision
from flint import arb,acb,acb_series,ctx
from .interval_chain import IntervalK10
from .verified_flow import integrate
from .verified_normal import horizontal_field,return_field
from .verified_moser import suspension
from .direct_cubic_bridge import DirectCubicBridge
from .arb_cache import ball_key
from .cubic_pole_inverse import local_coordinate,near_pole
from .cubic_atlas_inverse import atlas_inverse


class OutsideNormalImage(Exception):
    """Reverse horizontal moment is certified above the K10 fibre bound."""


def reverse_field(field):
    def reversed_field(time,state):return [-x for x in field(1-time,state)]
    reversed_field.jacobian=lambda time,state:-field.jacobian(1-time,state)
    return reversed_field


def normal_from_ball(point,d,h,**options):
    """Inverse normal transfer, with certified early exclusion at p>h.

    During reverse horizontal flow |W| increases, since its forward rate
    is -t W/(b D). A point crossing p=h cannot originate in D(h).
    """
    with ctx.workprec(options.get('bits',256)):
        point=list(map(arb,point));d,h=arb(d),arb(h)
        pi=arb.pi()
        positive=1-pi*sum(x*x for x in point)
        if not positive > 0:raise ArithmeticError('refine the ball chart or prove exclusion from the compact image')
        Z=[acb(positive.sqrt()),pi.sqrt()*acb(point[0],point[2]),pi.sqrt()*acb(point[1],point[3])]
        graph=integrate(reverse_field(return_field(d)),[z.real for z in Z]+[z.imag for z in Z],**options)
        Z=[acb(graph.endpoint[j],graph.endpoint[j+3]) for j in range(3)]
        norm=sum(abs(z)*abs(z) for z in Z).sqrt();Z=[z/norm for z in Z]
        W=sum(z*z*z for z in Z)
        initial=[*Z,W]
        def event(time,state):
            w2=state[3]*state[3]+state[7]*state[7]
            moment=d*w2/(1+w2)
            if moment.lower()>h.upper():
                raise OutsideNormalImage('reverse horizontal moment is certified greater than h')
        event(arb(0),[z.real for z in initial]+[z.imag for z in initial])
        normal=integrate(reverse_field(horizontal_field(d)),
            [z.real for z in initial]+[z.imag for z in initial],event=event,**options)
        Z=[acb(normal.endpoint[j],normal.endpoint[j+4]) for j in range(3)]
        W=acb(normal.endpoint[3],normal.endpoint[7])
        norm=sum(abs(z)*abs(z) for z in Z).sqrt()
        return [z/norm for z in Z],W/(norm*norm*norm),dict(
            accepted_steps=graph.accepted_steps+normal.accepted_steps,
            rejected_steps=graph.rejected_steps+normal.rejected_steps)


def torus_from_normal(bridge,Z,W,d):
    """Invert the actual Weierstrass parametrization, modulo its lattice."""
    C=bridge.cubic
    denominator=Z[1]+Z[2]
    pole=near_pole(Z)
    if pole:
        branches=[local_coordinate(C,Z)]
    else:
        if denominator.contains(0):raise ArithmeticError('refine the inverse at the Weierstrass pole')
        wp=-Z[0]/(C.cF*denominator)
        wpp=-(Z[2]-Z[1])/(C.dF*denominator)
        inverse=wp.elliptic_inv_p(C.tau);branches=[]
        if inverse.is_finite():
            for z in (inverse,-inverse):
                derivative=acb_series([z,1],prec=2).elliptic_p(C.tau)[1]
                if derivative.overlaps(wpp):branches.append(z)
        broad=(not branches or max(max(z.real.rad(),z.imag.rad()) for z in branches)>arb(2)**(-min(64,C.bits//8)))
        if broad:
            seeds=[]
            if inverse.is_finite():
                seeds=[inverse.mid()]
                seeds += [acb(x,y) for x in [inverse.real.lower(),inverse.real.upper()]
                          for y in [inverse.imag.lower(),inverse.imag.upper()]]
            branches=[atlas_inverse(C,Z,seeds=seeds)]
    candidates=[]
    for z in branches:
        v=z.imag/C.imtau;u=z.real-C.tau.real*v
        # A lattice representative is sufficient: every later flat stage
        # respects the clutch, and the last canonicalization removes it.
        u-=floor_mid(u);v-=floor_mid(v)
        ZA=C.unit_lift_A(u,v)
        alpha=sum(a.conjugate()*z for a,z in zip(ZA,Z))
        if alpha.contains(0):raise ArithmeticError('the recovered cubic gauge is unresolved')
        old_W=W/(alpha*alpha*alpha)
        fibre=arb(d).sqrt()*old_W/(C.pi.sqrt()*(1+abs(old_W)*abs(old_W)).sqrt())
        U=bridge.R(u+v,v)/bridge.M(v);V=bridge.V(v)
        fibre*=(-acb(0,6*C.pi)*bridge.G(u+v,v)).exp()
        candidates.append([U,V,fibre.real,fibre.imag])
    if not candidates:raise ArithmeticError('neither elliptic inverse branch matches the cubic derivative')
    return candidates


class InverseK10(IntervalK10):
    def fibre_cutoff(self):
        # Every nontrivial planar/Moser fibre motion is supported in the
        # eccentric disk B(c,rout); origin-centred rotations preserve I.
        # The entire open source neighbourhood has capacity rho_bar.
        m=self.strip.mu/3+self.strip.V0/(2*self.strip.M+1)
        rho_bar=(arb(self.P.rho)+min(arb(self.P.rho)+(self.strip.delta-m)/2,
                                   self.a-self.strip.delta))/2
        bound=arb(5)/16
        support_radius=arb(self.data['rout']**2).sqrt()
        support=arb.pi()*(arb(self.data['center'])+support_radius)**2
        if not max(rho_bar.upper(),support.upper())<bound or not bound<arb(self.P.h):
            raise ArithmeticError('K10 compact fibre bound was not certified')
        return bound

    def inverse_target(self,point,accuracy='1e-8',max_step='.0078125'):
        """Recover the common canonical layer target, before slot selection."""
        with ctx.workprec(self.bits):
            point=list(map(arb,point));sigma=arb(self.numeric.sigma)
            key=(tuple(ball_key(x) for x in point),ball_key(arb(accuracy)),ball_key(arb(max_step)),self.bits)
            cache=getattr(self,'_inverse_targets',{})
            if key in cache:return cache[key]
            def finish(targets,stats):
                if len(cache)>=64:cache.clear()
                cache[key]=(targets,stats)
                self._inverse_targets=cache
                return targets,stats
            if all(x.is_zero() for x in point):
                # The origin is the projective point [1:0:0]. Both normal
                # fields have N=0 there, and the return field fixes it.
                # Reverse horizontal flow keeps Z=[1:0:0] for t>0,
                # whereas the initial cubic has sum(Z_j^3)=0. Thus this
                # point has no normal-bundle preimage. This is an exact
                # geometric exclusion, independent of failed solves.
                return finish(None,dict(excluded='the projective coordinate axis is outside the normal image'))
            if sum(x*x for x in point).lower()>(arb(73)/40)**2:
                return finish(None,dict(excluded='outside the certified target radius'))
            options=dict(bits=self.bits,order=max(24,self.bits//16),max_step=max_step,
                         max_radius=accuracy,remainder_guard_bits=128+64*getattr(self,'retry_index',0),
                         max_steps=max(100000,self.bits**3))
            if self.progress:options['progress']=lambda info:self.progress('inverse_flow',info)
            try:Z,W,stats=normal_from_ball([sigma*x for x in point],self.P.d,self.fibre_cutoff(),**options)
            except OutsideNormalImage as error:return finish(None,dict(excluded=str(error)))
            if self.progress:self.progress('inverse_normal',stats)
            bridge=DirectCubicBridge(bits=self.bits,root_bits=root_precision(self.bits,accuracy),workers=1)
            candidates=torus_from_normal(bridge,Z,W,self.P.d)
            targets=[]
            for state in candidates:
                if not self.I(state[2:]).upper()<arb(self.P.h):
                    raise ArithmeticError('refine the recovered fibre domain before the flat inverse')
                if self.progress:self.progress('inverse_landau',dict(max_radius=max(float(x.rad()) for x in state)))
                state=self.base_forward(self.shear_forward(state))
                if self.progress:self.progress('inverse_base',dict(max_radius=max(float(x.rad()) for x in state)))
                flow=suspension(state,self.P,self.data,inverse=False,local_frame=True,**options)
                state=self.layer_forward(flow.endpoint)
                u,v,*z=state;n=floor_mid(u)
                u-=n;z=self.rotate(z,-n*(9*v+arb(3)/2))
                targets.append([u,v,*z])
            return finish(targets,stats)

    def inverse(self,point,index,accuracy='1e-8',max_step='.0078125'):
        with ctx.workprec(self.bits):
            targets,stats=self.inverse_target(point,accuracy,max_step)
            if targets is None:return None,stats
            results=[];discarded_branch=False
            sigma=arb(self.numeric.sigma)
            for target in targets:
                u=target[0]
                start=arb(self.numeric.model.ball_layer.starts[index]);end=start+arb(self.numeric.model.ball_layer.width)
                if u.upper()<start.lower() or u.lower()>end.upper():
                    discarded_branch=True
                    continue
                source=self.ball_layer_inverse(target,index)
                results.append([x/sigma for x in source])
            if not results:return None,dict(excluded='inverse belongs to a different ball-layer slot',**stats)
            if discarded_branch:
                raise ArithmeticError('refine the elliptic branches before deciding the ball-layer slot')
            result=results[0]
            for row in results[1:]:result=[a.union(b) for a,b in zip(result,row)]
            if max(x.rad() for x in result)>arb(accuracy):raise ArithmeticError('inverse source enclosure requires refinement')
            return result,stats
