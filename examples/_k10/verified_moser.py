"""Real interval/jet version of the autonomous k10 suspension vector field.

The floor choices are checked on whole input boxes. Flat-step seams use
real derivative bounds from interval_bump, not analytic continuation.
"""
import math
from .arb_cache import floor_mid,nearest_mid

from flint import arb, arb_mat, arb_series, ctx
from .dual import Dual
from .interval_bump import step_jet
from .verified_flow import integrate


def rotate(z, angle):
    c, s = angle.cos(), angle.sin()
    return [c*z[0]-s*z[1], s*z[0]+c*z[1]]


def _constant(value, precision):
    return arb_series([value], prec=precision)


def base_geometry(v):
    # Exact thirds define the marked fibres; float evaluation approximates
    # these constants. Use exact Arb divisions in this verified evaluator.
    n = floor_mid(v[0])
    local, precision = v-n, v.prec
    collar = arb(1)/48
    for j in range(4):
        centre = arb(j)/3
        if abs(local[0]-centre).upper() < collar:
            return _constant(n+centre, precision), _constant(0, precision)
    for j in range(3):
        left, right = arb(j)/3, arb(j+1)/3
        if local[0].lower() >= left and local[0].upper() <= right:
            width = right-left-2*collar
            argument = (local-left-collar)/width
            return n+left+(right-left)*step_jet(argument), (right-left)/width*step_jet(argument, 1)
    raise ValueError('base interval spans more than one puncture collar')


def suspension_field(parameters, path_data, *, inverse=False, local_frame=False):
    # All displayed constants except marked thirds/pi are the stored
    # parameter values interpreted as exact binary real numbers.
    e, h = arb(parameters.e), arb(parameters.h)
    centre = arb(path_data['center'])
    inner, outer = arb(path_data['rin']**2), arb(path_data['rout']**2)
    gap, pi = outer-inner, arb.pi()
    ku = arb(3)/2
    start, width_u = arb(.4), arb(.2)
    def field(clock, state):
        lam = 1-clock if inverse else clock
        u, v, q, p = state
        precision = u.prec
        n = floor_mid(u[0])
        local_u = u-n
        if local_u[0].upper() <= start or local_u[0].lower() >= start+width_u:
            return [_constant(0, precision) for _ in range(4)]
        if not (local_u[0].lower() >= 0 and local_u[0].upper() <= 1):
            raise ValueError('active suspension box crosses a developed u cell')
        argument = (local_u-start)/width_u
        F, Fp = step_jet(argument), step_jet(argument, 1)/width_u
        B, b = base_geometry(v)
        turns = -9*u*(v-B)-n*(9*B+ku)
        z = [q,p] if local_frame else rotate([q, p], 2*pi*turns)
        w = [z[0]-centre, z[1]]
        r2 = w[0]*w[0]+w[1]*w[1]
        radial_argument = (r2-inner)/gap
        chi = 1-step_jet(radial_argument)
        chip, chipp = -step_jet(radial_argument, 1), -step_jet(radial_argument, 2)
        speed = pi*(chi+(r2-outer)*chip/gap)
        speedp = pi*(2*chip/gap+(r2-outer)*chipp/(gap*gap))
        tau = lam*(F-1)
        r = rotate(w, tau*speed)
        r[0] += centre
        moment = pi*(r[0]*r[0]+r[1]*r[1])
        H = 3-9*moment-e
        denominator = e+Fp*H*b
        pdot = -2*pi*centre*speed*r[1]
        udot = 9*F*(F-1)*pdot*b/denominator
        Q = pi/2*(r2-outer)*chi
        vdot = Fp*Q/denominator
        co, si = (tau*speed).cos(), (tau*speed).sin()
        out_y = si*w[0]+co*w[1]
        gradient = [2*pi*(w[0]+centre*co-2*tau*speedp*centre*out_y*w[0]),
                    2*pi*(w[1]-centre*si-2*tau*speedp*centre*out_y*w[1])]
        Xp = [-gradient[1], gradient[0]]
        velocity = [-speed*w[1], speed*w[0]]
        local_dot = [9*F*b*vdot*x-lam*Fp*udot*y for x, y in zip(Xp, velocity)]
        Lu, Lv = -9*(v-B), -9*(u*(1-b)+n*b)
        angle_dot = -2*pi*(Lu*udot+Lv*vdot)
        if local_frame:
            result=[udot,vdot,*local_dot]
        else:
            fibre_dot = rotate(local_dot, -2*pi*turns)
            result = [udot, vdot, fibre_dot[0]-angle_dot*p, fibre_dot[1]+angle_dot*q]
        return [-x for x in result] if inverse else result
    def jacobian(time, values):
        state = [Dual(arb_series([x], prec=1),
                      [arb_series([int(i == j)], prec=1) for j in range(4)]) for i, x in enumerate(values)]
        result = field(arb_series([time], prec=1), state)
        return arb_mat([[x.gradient[j][0] if isinstance(x, Dual) else 0 for j in range(4)] for x in result])
    field.jacobian = jacobian
    return field


def change_frame(state,*,to_local=True,cell=None):
    u,v,q,p=state
    n=floor_mid(u) if cell is None else cell
    B,_=base_geometry(arb_series([v],prec=1));B=B[0]
    turns=9*u*(v-B)+n*(9*B+arb(3)/2)
    z=rotate([q,p],(-1 if to_local else 1)*2*arb.pi()*turns)
    return [u,v,*z]


def suspension(initial, parameters, path_data, *, inverse=False,local_frame=False, **options):
    with ctx.workprec(options.get('bits', 256)):
        if not local_frame:
            return integrate(suspension_field(parameters, path_data, inverse=inverse), initial, **options)
        from dataclasses import replace
        cell=floor_mid(initial[0])
        result=integrate(suspension_field(parameters,path_data,inverse=inverse,local_frame=True),
                         change_frame(initial,cell=cell),**options)
        return replace(result,endpoint=tuple(change_frame(result.endpoint,to_local=False,cell=cell)))
