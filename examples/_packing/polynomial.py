"""Evaluate the finite global Hamiltonian returned by the Lean certificate search.

Coordinates are (q1,q2,p1,p2), matching verification/Problem.lean.
H(t,y)=boxCut(B,y)*P(t,y) on ALL real times. Clipping is confined to
the internal polynomial-field verifier, not this output Hamiltonian.
This evaluator does not certify that an arbitrary supplied polynomial packs.
"""
from fractions import Fraction
from math import isqrt
from flint import arb, arb_series, ctx
from .dual import Dual
from .rational import rational
from .bump import step_jet


def nat_pair(a, b):
    if any(isinstance(x, bool) or not isinstance(x, int) or x < 0 for x in [a, b]):
        raise ValueError('natural-number codes required')
    return b*b+a if a < b else a*a+a+b


def nat_unpair(code):
    if isinstance(code, bool) or not isinstance(code, int) or code < 0:
        raise ValueError('natural-number code required')
    s = isqrt(code); tail = code-s*s
    return (tail, s) if tail < s else (s, tail-s)


def rational_value(code):
    numerator, denominator = nat_unpair(code)
    positive, negative = nat_unpair(numerator)
    return Fraction(positive-negative, denominator+1)


def rational_code(value):
    q = Fraction(value)
    return nat_pair(nat_pair(max(q.numerator, 0), max(-q.numerator, 0)), q.denominator-1)


def polynomial(program, coordinates):
    """The exact tail-first prefix-stack semantics, including underflow."""
    zero = coordinates[0]*0; stack = []
    for command in reversed(program):
        tag, payload = nat_unpair(command)
        if tag == 0:
            stack.insert(0, zero+rational(rational_value(payload)))
        elif tag == 1:
            stack.insert(0, coordinates[payload] if payload < len(coordinates) else zero)
        else:
            a = stack[0] if stack else zero
            b = stack[1] if len(stack) > 1 else zero
            stack = [a+b if tag == 2 else a*b]+stack[2:]
    return stack[0] if stack else zero


def program_budget(B, program):
    stack = []
    for command in reversed(program):
        tag, payload = nat_unpair(command)
        if tag == 0:
            positive, negative = nat_unpair(nat_unpair(payload)[0])
            stack.insert(0, positive+negative+2)
        elif tag == 1:
            stack.insert(0, B+2)
        else:
            a = stack[0] if stack else 2
            b = stack[1] if len(stack) > 1 else 2
            stack = [a+b if tag == 2 else 4*a*b]+stack[2:]
    return stack[0] if stack else 2


class FinitePolynomialHamiltonian:
    def __init__(self, B, program):
        if isinstance(B, bool) or not isinstance(B, int) or B < 1:
            raise ValueError('positive integer cutoff box required')
        self.B = B; self.program = tuple(program)
        for command in self.program:
            nat_unpair(command)

    def jet(self, time, point):
        if len(point) != 4 or not isinstance(time, arb_series):
            raise ValueError('one time jet and four grouped phase-coordinate jets required')
        precision = time.prec
        if any(not isinstance(v, arb_series) or v.prec != precision for v in point):
            raise ValueError('complete equal-precision input jets required')
        if any(not v[j].is_finite() for v in [time, *point] for j in range(precision)):
            raise ValueError('finite complete real input coefficients required')
        zero = time*0; one = zero+1
        coordinates = [Dual(time, [zero]*4)]
        coordinates += [Dual(v, [one if i == j else zero for j in range(4)]) for i, v in enumerate(point)]
        cutoff = coordinates[0]*0+1
        # Exact same square-based cutoff as SymplecticPacking/E4.lean.
        lower = rational(Fraction(self.B, 2))
        upper = rational(Fraction(3*self.B, 4))
        for coordinate in coordinates[1:]:
            u = (coordinate*coordinate-lower*lower)/(upper*upper-lower*lower)
            cutoff *= 1-step_jet(u)
        if (all(cutoff.value[j].is_zero() for j in range(precision))
                and all(v[j].is_zero() for v in cutoff.gradient for j in range(precision))):
            return dict(value=zero, gradient=[zero]*4, vector_field=[zero]*4)
        result = cutoff*polynomial(self.program, coordinates)
        gradient = result.gradient
        return dict(value=result.value, gradient=gradient,
                    vector_field=[gradient[2], gradient[3], -gradient[0], -gradient[1]])

    def evaluate(self, time, point, *, bits=256):
        with ctx.workprec(bits):
            old = ctx.cap; ctx.cap = max(old, 8)
            try:
                to_ball = lambda v: rational(v) if isinstance(v, Fraction) else arb(v)
                result = self.jet(arb_series([to_ball(time)], prec=1),
                                  [arb_series([to_ball(v)], prec=1) for v in point])
                return dict(value=result['value'][0], gradient=[v[0] for v in result['gradient']],
                            vector_field=[v[0] for v in result['vector_field']])
            finally:
                ctx.cap = old

    def value_gradient(self, time, point, *, tolerance='1e-8', initial_bits=256):
        """Certified scalar-point evaluation, increasing precision without a cap.

        Fixed nonzero-width input boxes should use ``jet`` or ``evaluate``;
        increasing arithmetic precision cannot remove their true variation.
        """
        def exact_scalar(v):
            if isinstance(v, arb):
                if not v.is_finite() or not v.is_exact():
                    raise ValueError('scalar-point evaluation requires exact finite inputs')
                m, e = map(int, v.man_exp())
                return Fraction(m*(1 << e)) if e >= 0 else Fraction(m, 1 << -e)
            return Fraction(v)
        time = exact_scalar(time); point = list(map(exact_scalar, point))
        if not isinstance(initial_bits, int) or initial_bits < 32:
            raise ValueError('initial precision must be an integer at least32')
        bits = initial_bits
        while True:
            with ctx.workprec(bits):
                goal = rational(Fraction(tolerance))
                if not goal > 0:
                    raise ValueError('positive rational output tolerance required')
                result = self.evaluate(time, point, bits=bits)
                if all(v.is_finite() and v.rad() <= goal for v in [result['value'], *result['gradient']]):
                    return dict(result, bits=bits)
            bits *= 2
