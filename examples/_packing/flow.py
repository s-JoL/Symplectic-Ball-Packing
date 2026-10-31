"""Validated real ODE evaluation by Picard tubes and Taylor remainders.

The caller supplies the SAME smooth real vector field on Arb balls and on
Arb Taylor jets. No floating trajectory or convergence heuristic is used
as an error bound. This is a local evaluator, not a whole-domain proof.
"""
from dataclasses import dataclass

from flint import arb, arb_series, ctx


@dataclass
class FlowEnclosure:
    endpoint: tuple
    accepted_steps: int
    rejected_steps: int
    bits: int
    order: int


def _dyadic_below(value):
    value=arb(value).lower()
    if not value>0:raise ValueError('a positive step bound is required')
    man,exp=value.man_exp()
    return arb(2)**(int(exp)+int(man).bit_length()-1)


def _jet(field, time, initial, order):
    coefficients = [[arb(x)] for x in initial]
    for k in range(order):
        t = arb_series([time, 1], prec=k+1)
        y = [arb_series(c, prec=k+1) for c in coefficients]
        f = field(t, y)
        if len(f) != len(coefficients) or any(value.prec < k+1 for value in f):
            raise ArithmeticError('vector field returned an incomplete Taylor jet')
        for c, value in zip(coefficients, f):
            c.append(value[k]/(k+1))
    return coefficients


def _point_field(field, time, values):
    return [value[0] for value in field(arb_series([time], prec=1),
                                       [arb_series([x], prec=1) for x in values])]


def _tube(field, time, initial, step):
    interval = arb(step/2, step/2)
    tbox = time+interval
    try:
        f0 = _point_field(field, time, initial)
    except (ValueError, ZeroDivisionError):
        return None
    tiny = arb(2)**(-ctx.prec+16)
    tube = [arb(x.mid(), (x.rad()+2*step*abs(f)+tiny).upper()) for x, f in zip(initial, f0)]
    # Variational coordinates can have a zero first velocity but a nonzero
    # higher-order velocity. Allow the componentwise tube iteration to
    # transport that uncertainty before reducing the step.
    for _ in range(32):
        try:
            f = _point_field(field, tbox, tube)
        except (ValueError, ZeroDivisionError):
            return None
        proposal = [x+interval*v for x, v in zip(initial, f)]
        if all(box.is_finite() and box.contains_interior(value) for box, value in zip(tube, proposal)):
            return tbox, tube
        if not all(x.is_finite() for x in proposal):
            return None
        # Keep a component once it already encloses its Picard image.
        # Enlarging every component while a one-way action coordinate
        # catches up can make that coordinate's bound grow faster than
        # its tube, and can needlessly cross a valid spatial chart.
        # The final simultaneous self-containment test is unchanged.
        tube = [box if box.contains_interior(value) else
                arb(x.mid(), 1.25*max(abs(box-x.mid()).upper(),abs(value-x.mid()).upper())+tiny)
                for x,box,value in zip(initial,tube,proposal)]
    return None


def integrate(field, initial, end=1, *, bits=160, order=16, max_step='0.015625',
              max_radius='1e-10', max_steps=100000, progress=None, remainder_guard_bits=64,event=None):
    """Enclose the real flow from t=0 to end, or fail explicitly.

    All time steps are exact dyadics except an exact final remainder. The
    requested maximum radius is an acceptance requirement, not a claimed
    bound inferred from floating tolerances. Initial data may be balls.
    """
    previous_cap = ctx.cap
    ctx.cap = max(previous_cap, order+5)
    try:
        with ctx.workprec(bits):
            y, time, end = list(map(arb, initial)), arb(0), arb(end)
            if not end.is_exact() or not end > 0:
                raise ValueError('end must be a positive exact real')
            # A full-precision dyadic midpoint may need additional
            # mantissa bits after repeated addition. Powers of two keep
            # the mesh clock exact; the final remainder is exact by
            # subtraction near the endpoint.
            step_limit = _dyadic_below(arb(max_step))
            step = step_limit
            radius_limit = arb(max_radius)
            accepted = rejected = 0
            while time < end:
                if accepted+rejected >= max_steps:
                    raise ArithmeticError('validated flow step budget exhausted')
                h = min(step, end-time)
                if not h.is_exact() or not (time+h).is_exact():
                    raise ArithmeticError('more precision is required to keep the flow mesh clock exact')
                enclosure = _tube(field, time, y, h)
                if enclosure is None:
                    step = _dyadic_below(h/2)
                    rejected += 1
                    if step < arb(2)**(-bits//2):
                        raise ArithmeticError('no positive Picard tube could be certified')
                    continue
                tbox, tube = enclosure
                try:
                    jet = _jet(field, time, y, order)
                    remainder = _jet(field, tbox, tube, order+1)
                except (ValueError, ZeroDivisionError):
                    # A range tube can exist while a higher real jet
                    # still needs a smaller spatial box (e.g. a series
                    # denominator enclosure straddles zero). This is a
                    # rejected step, not a failed exact trajectory.
                    step = _dyadic_below(h/2)
                    rejected += 1
                    if step < arb(2)**(-bits//2):
                        raise ArithmeticError('no complete real flow jet could be certified')
                    continue
                if max(abs(c[-1]*h**(order+1)).upper() for c in remainder) > radius_limit*h/(128*2**remainder_guard_bits*end):
                    step = _dyadic_below(h/2)
                    rejected += 1
                    continue
                out = []
                for coefficients, error in zip(jet, remainder):
                    value = arb(0)
                    for coefficient in reversed(coefficients):
                        value = value*h+coefficient
                    out.append(value+error[-1]*h**(order+1))
                if not all(x.is_finite() and x.rad() < radius_limit for x in out):
                    # Shrinking the current step cannot repair uncertainty
                    # that has already accumulated in its initial ball.
                    if max(x.rad() for x in y) > radius_limit/2:
                        raise ArithmeticError('interval wrapping exceeds requested output radius')
                    step = _dyadic_below(h/2)
                    rejected += 1
                    continue
                y, time = out, time+h
                accepted += 1
                if event is not None:
                    event(time,y)
                if accepted % 4 == 0:
                    step = min(2*h, step_limit)
                if progress is not None and accepted % 100 == 0:
                    progress(dict(time=float(time.mid()), step=float(h.mid()),
                                  accepted_steps=accepted, rejected_steps=rejected,
                                  maximum_radius=max(float(x.rad()) for x in y)))
            return FlowEnclosure(tuple(y), accepted, rejected, bits, order)
    finally:
        ctx.cap = previous_cap
