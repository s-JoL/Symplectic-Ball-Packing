"""Real Taylor quadrature with a rigorous remainder for C-infinity data.

Unlike complex analytic quadrature, this can cross flat-step seams. The
integrand must implement valid real interval Taylor jets, including seams.
"""
from dataclasses import dataclass

from flint import arb, arb_series, ctx


@dataclass
class IntegralEnclosure:
    value: arb
    panels: int
    bits: int
    order: int


def integrate(function, a, b, *, tolerance='1e-20', bits=160, order=16, max_panels=None,
              strict_radius=True):
    if order < 2 or order % 2:
        raise ValueError('use a positive even Taylor remainder order')
    previous_cap = ctx.cap
    ctx.cap = max(previous_cap, order+4)
    try:
        with ctx.workprec(bits):
            a, b, tolerance = arb(a), arb(b), arb(tolerance)
            max_panels = max(100000, bits**3) if max_panels is None else max_panels
            if not a.is_finite() or not b.is_finite() or not b-a > 0:
                raise ValueError('need ordered finite real endpoints')
            start, end = a.mid(), b.mid()
            pending, result, panels = [(start, end)], arb(0), 0
            while pending:
                left, right = pending.pop()
                centre, radius = (left+right)/2, (right-left)/2
                if not (centre.lower() > left.upper() and centre.upper() < right.lower()):
                    raise ArithmeticError('more precision is required to subdivide this integral')
                interval = arb(centre, radius)
                try:
                    bound_jet = function(arb_series([interval, 1], prec=order+1))
                    if bound_jet.prec < order+1:
                        raise ArithmeticError('integrand returned an incomplete remainder jet')
                    bound = bound_jet[order]
                except (ValueError, ZeroDivisionError):
                    bound = arb('nan')
                error = 2*radius**(order+1)/(order+1)*abs(bound)
                if error.is_finite() and error < tolerance*(right-left)/(end-start)/8:
                    jet = function(arb_series([centre, 1], prec=order))
                    if jet.prec < order:
                        raise ArithmeticError('integrand returned an incomplete Taylor jet')
                    value = arb(0)
                    for k in range(0, order, 2):
                        value += 2*jet[k]*radius**(k+1)/(k+1)
                    # Even-order remainder has a nonnegative integration
                    # weight; a symmetric error ball is sufficient here.
                    result += value+arb(0, error.upper())
                    panels += 1
                else:
                    if panels+len(pending)+2 > max_panels:
                        raise ArithmeticError('validated quadrature panel budget exhausted')
                    pending.extend([(left, centre), (centre, right)])
            # Exact real endpoints may be represented by balls. Enclose the
            # short uncertain end pieces independently of the midpoint mesh.
            for endpoint, sign in [(a, -1), (b, 1)]:
                if endpoint.rad() != 0:
                    value = function(arb_series([endpoint], prec=1))[0]
                    result += sign*(endpoint-endpoint.mid())*value
            if not result.is_finite() or (strict_radius and result.rad() > tolerance):
                raise ArithmeticError('quadrature uncertainty exceeds requested tolerance')
            return IntegralEnclosure(result, panels, bits, order)
    finally:
        ctx.cap = previous_cap
