"""Validated formal Newton doubling for an implicit real Taylor jet.

The constant enclosure must contain the true implicit root and the
derivative lower bound must hold there. If m coefficients contain the
true jet, Newton's formal identity certifies 2m coefficients. Interval
arithmetic encloses that polynomial computation; old coefficients are
intersected only with other independently valid enclosures.
"""
from flint import arb,arb_series,ctx


def solve(constant,precision,equation,derivative_lower):
    previous=ctx.cap;ctx.cap=max(previous,precision+4)
    try:
        current=arb_series([constant],prec=1);known=1
        while known<precision:
            size=min(2*known,precision)
            trial=arb_series([current[j] for j in range(known)],prec=size)
            residual,derivative=equation(trial,size)
            # The actual, unknown coefficients represented by `current`
            # solve the equation modulo x^known. These residual
            # coefficients are therefore EXACTLY zero, even when naive
            # interval evaluation loses their parameter correlations.
            for j in range(known):residual[j]=arb(0)
            lower=max(derivative[0].lower(),arb(derivative_lower).lower());upper=derivative[0].upper()
            if not lower>0 or upper<lower:raise ValueError('subdivide the box to certify the implicit jet derivative')
            derivative[0]=arb((lower+upper)/2,(upper-lower)/2)
            refined=trial-residual/derivative
            if refined.prec<size:raise ArithmeticError('implicit Newton jet was silently truncated')
            coefficients=[constant]
            for j in range(1,size):
                coefficients.append(refined[j].intersection(current[j]) if j<known else refined[j])
            current=arb_series(coefficients,prec=size);known=size
        return current
    finally:ctx.cap=previous
