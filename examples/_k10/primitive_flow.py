"""Validated primitive integrals along the actual real transfer ODEs.

The extra scalar is a triangular ODE coordinate. Its derivative and its
Lohner transition are enclosed along with the physical flow; a numerical
phase unwrap is never used as a certificate.
"""
import math
from .arb_cache import floor_mid,nearest_mid
from flint import arb, arb_mat, arb_series, acb, ctx
from .dual import Dual
from .verified_flow import integrate
from .lohner import triangular_transition
from .verified_normal import _complex, _parts, horizontal_field, return_field
from .verified_moser import base_geometry, rotate, suspension_field,change_frame
from .interval_bump import step_jet


def primitive_field(field, size, rate):
    def augmented(time,state):
        point=state[:size]
        velocity=field(time,point)
        return velocity+[rate(time,point,velocity)]
    def jacobian(time,state):
        values=[Dual(arb_series([x],prec=1),
                     [arb_series([int(i==j)],prec=1) for j in range(size)])
                for i,x in enumerate(state[:size])]
        t=arb_series([time],prec=1)
        velocity=field(t,values)
        extra=rate(t,values,velocity)
        rows=[]
        for value in velocity+[extra]:
            rows.append(([x[0] for x in value.gradient] if isinstance(value,Dual)
                         else [arb(0)]*size)+[arb(0)])
        return arb_mat(rows)
    augmented.jacobian=jacobian
    augmented.error_blocks=[list(range(size)),[size]]
    augmented.transition=lambda J,h:triangular_transition(J,h,size)
    return augmented


def phase_rate(size):
    def rate(time,state,velocity):
        z0=_complex(state[0],state[size])
        dz0=_complex(velocity[0],velocity[size])
        return -_parts(dz0/z0)[1]/(2*arb.pi())
    return rate


def moser_rate(parameters,path_data,*,inverse=False,local_frame=False):
    e=arb(parameters.e)
    centre=arb(path_data['center'])
    inner,outer=arb(path_data['rin']**2),arb(path_data['rout']**2)
    gap=outer-inner
    def rate(time,state,velocity):
        lam=1-time if inverse else time
        u,v,q,p=state
        n=floor_mid(u[0])
        local=u-n
        if local[0].upper() <= arb(.4) or local[0].lower() >= arb(.6):
            return u*0
        F=step_jet((local-arb(.4))/arb(.2))
        Fp=step_jet((local-arb(.4))/arb(.2),1)/arb(.2)
        B,b=base_geometry(v)
        z=[q,p] if local_frame else rotate([q,p],-2*arb.pi()*(9*u*(v-B)+n*(9*B+arb(3)/2)))
        w=[z[0]-centre,z[1]]
        r2=w[0]*w[0]+w[1]*w[1]
        chi=1-step_jet((r2-inner)/gap)
        chip=-step_jet((r2-inner)/gap,1)
        speed=arb.pi()*(chi+(r2-outer)*chip/gap)
        # q_{lam(F-1)}(z) has the same eccentric radius and Q as z.
        r=rotate(w,lam*(F-1)*speed);r[0]+=centre
        Q=arb.pi()/2*(r2-outer)*chi
        Hphysical=3-9*arb.pi()*(q*q+p*p)-e
        Hpulled=3-9*arb.pi()*(r[0]*r[0]+r[1]*r[1])-e
        if local_frame:
            # Pull back the physical primitive as a covector. The fibre
            # rotation contributes I(z) d[9u(v-B)+n(9B+3/2)].
            au=lam*Fp*Q+(3-e)*(v-B)
            av=e*u+F*Hpulled*b+(3-e)*(u*(1-b)+n*b)
        else:
            au=lam*Fp*Q+Hphysical*(v-B)
            av=e*u+F*Hpulled*b+Hphysical*(u*(1-b)+n*b)
        form=[au,av,-p/2,q/2]
        return sum(a*v for a,v in zip(form,velocity))
    return rate


def suspension_action(initial,parameters,path_data,*,inverse=False,action=0,local_frame=False,**options):
    with ctx.workprec(options.get('bits',256)):
        cell=floor_mid(initial[0])
        data=change_frame(initial,cell=cell) if local_frame else initial
        field=suspension_field(parameters,path_data,inverse=inverse,local_frame=local_frame)
        rate=moser_rate(parameters,path_data,inverse=inverse,local_frame=local_frame)
        result=integrate(primitive_field(field,4,rate),[*data,action],**options)
        endpoint=(change_frame(result.endpoint[:4],to_local=False,cell=cell)
                  if local_frame else result.endpoint[:4])
        return endpoint,result.endpoint[4],result


def normal_to_ball_action(initial,d,action=0,**options):
    with ctx.workprec(options.get('bits',256)):
        initial=list(map(acb,initial))
        state=[z.real for z in initial]+[z.imag for z in initial]
        horizontal=integrate(primitive_field(horizontal_field(d),8,phase_rate(4)),
                             state+[action],**options)
        Z=[acb(horizontal.endpoint[j],horizontal.endpoint[j+4]) for j in range(3)]
        norm=sum(abs(z)*abs(z) for z in Z).sqrt()
        Z=[z/norm for z in Z]
        returned=integrate(primitive_field(return_field(d),6,phase_rate(3)),
                           [z.real for z in Z]+[z.imag for z in Z]+[horizontal.endpoint[8]],**options)
        Z=[acb(returned.endpoint[j],returned.endpoint[j+3]) for j in range(3)]
        norm=sum(abs(z)*abs(z) for z in Z).sqrt()
        q=[z*Z[0].conjugate()/(norm*abs(Z[0])*arb.pi().sqrt()) for z in Z[1:]]
        return [z.real for z in q]+[z.imag for z in q],returned.endpoint[6],dict(
            accepted_steps=horizontal.accepted_steps+returned.accepted_steps,
            rejected_steps=horizontal.rejected_steps+returned.rejected_steps)
