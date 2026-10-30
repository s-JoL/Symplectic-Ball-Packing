"""C-infinity flat steps on Arb jets, including boxes crossing the seams.

At a seam, analytic continuation is unavailable. Explicit real derivative
bounds for exp(-1/x) supply Taylor jets instead; they are valid for every
real centre in the input interval. This module never treats the step as
analytic across 0 or 1.
"""
from functools import lru_cache
import math

from flint import arb, arb_series, ctx
from .dual import Dual


@lru_cache(None)
def _derivative_polynomial(n):
    # d^n exp(-1/x) = exp(-t) P_n(t), t=1/x.
    if n == 0:
        return {0: 1}
    previous = _derivative_polynomial(n-1)
    result = {}
    for k, coefficient in previous.items():
        result[k+2] = result.get(k+2, 0)+coefficient
        if k:
            result[k+1] = result.get(k+1, 0)-k*coefficient
    return {k: c for k, c in result.items() if c}


def _expflat_derivative(x, n):
    x = arb(x)
    if x.upper() <= 0:
        return arb(0)
    if n==0:
        return (-1/x).exp() if x>0 else arb(0).union((-1/x.upper()).exp())
    polynomial = _derivative_polynomial(n)
    if x>0 and x.upper()<=2*x.lower():
        t = 1/x
        value = arb(0)
        for k in range(max(polynomial), -1, -1):
            value = value*t+polynomial.get(k, 0)
        return (-t).exp()*value
    # Include x<=0, where every derivative vanishes. For x>0 let t=1/x.
    # Each t^m exp(-t) is maximal at max(m,1/x_upper).
    tmin = 1/x.upper()
    bound = arb(0)
    for m, coefficient in polynomial.items():
        t = max(arb(m), tmin)
        bound += abs(coefficient)*t**m*(-t).exp()
    return arb(0, bound.upper())


def step_jet(t, derivative=0):
    """S^(derivative)(t) for any finite nonnegative derivative order."""
    if not isinstance(derivative,int) or derivative<0:
        raise ValueError('a nonnegative integer derivative order is required')
    composer=getattr(t,'compose_step',None)
    if callable(composer):return composer(derivative)
    previous=ctx.cap
    # Seam evaluation first constructs S to precision+derivative before
    # shifting coefficients. A smaller global cap must never turn the
    # missing high coefficients into claimed exact zeros.
    ctx.cap=max(previous,t.prec+derivative+4)
    try:
        return _step_jet(t,derivative)
    finally:
        ctx.cap=previous


def _step_jet(t, derivative=0):
    if isinstance(t, Dual):
        value = step_jet(t.value, derivative)
        slope = step_jet(t.value, derivative+1)
        return Dual(value, [slope*x for x in t.gradient])
    a, precision = t[0], t.prec
    if a.upper() <= 0:
        return arb_series([], prec=precision)
    if a.lower() >= 1:
        return arb_series([1 if derivative == 0 else 0], prec=precision)
    if a.lower()>=arb(1)/2 and a.upper()>arb(1)/2:
        # Compute every small derivative from the small LEFT tail. Using
        # S*(1-S) near the right endpoint loses exponentially small values
        # through subtraction, even at very high working precision.
        reflected=step_jet(1-t,derivative)
        return 1-reflected if derivative==0 else (-1)**(derivative+1)*reflected
    if derivative>4:return _real_step_taylor(t,derivative)
    interior=(a>0 and 1-a>0)
    well_scaled=(interior and a.upper()<=2*a.lower() and (1-a).upper()<=2*(1-a).lower())
    if well_scaled:
        # Fast analytic formula when the entire centre box is interior.
        if a.upper()<=arb(1)/2:
            small=(-1/t+1/(1-t)).exp()
            S=small/(1+small)
        else:
            S = 1/(1+(1/t-1/(1-t)).exp())
        if derivative == 0:
            return S
        kp = 1/(t*t)+1/((1-t)*(1-t))
        first = S*(1-S)*kp
        if derivative == 1:
            return first
        kpp = -2/(t*t*t)+2/((1-t)*(1-t)*(1-t))
        if derivative == 2:
            return S*(1-S)*((1-2*S)*kp*kp+kpp)
        kppp = 6/(t*t*t*t)+6/((1-t)*(1-t)*(1-t)*(1-t))
        if derivative == 3:
            return S*(1-S)*((1-6*S+6*S*S)*kp*kp*kp+3*(1-2*S)*kp*kpp+kppp)
        kpppp = -24/(t*t*t*t*t)+24/((1-t)*(1-t)*(1-t)*(1-t)*(1-t))
        return S*(1-S)*((1-14*S+36*S*S-24*S*S*S)*kp*kp*kp*kp
            +6*(1-6*S+6*S*S)*kp*kp*kpp+3*(1-2*S)*kpp*kpp
            +4*(1-2*S)*kp*kppp+kpppp)
    return _real_step_taylor(t,derivative)


def _real_step_taylor(t,derivative):
    a,precision=t[0],t.prec
    count = precision+derivative
    f = arb_series([_expflat_derivative(a, n)/math.factorial(n) for n in range(count)], prec=count)
    g = arb_series([(-1)**n*_expflat_derivative(1-a, n)/math.factorial(n) for n in range(count)], prec=count)
    denominator=f+g
    # At least one of x and 1-x is >=1/2, so expflat(x)+
    # expflat(1-x)>=exp(-2) on the ENTIRE real line. Independent interval
    # evaluation of the two terms must retain this common lower bound.
    lo=max(denominator[0].lower(),arb(-2).exp().lower());hi=denominator[0].upper()
    if hi<lo:raise ArithmeticError('flat-step denominator contradicts its analytic lower bound')
    denominator[0]=arb((lo+hi)/2,(hi-lo)/2)
    S = f/denominator
    delta = arb_series([0]+[t[k] for k in range(1, precision)], prec=precision)
    result, power = arb_series([], prec=precision), arb_series([1], prec=precision)
    for k in range(precision):
        result += S[k+derivative]*(math.factorial(k+derivative)//math.factorial(k))*power
        power *= delta
    return result
