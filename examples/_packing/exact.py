"""Unbounded-integer rational fallback; no machine-word precision parameter.

Outward dyadic rounding after each operation prevents denominator explosion.
Only integer arithmetic, Fraction, alternating exponential series and interval
Picard/Euler steps are used. This is a reference algorithm, not a fast solver.
"""
from fractions import Fraction

from .dual import Dual
from .polynomial import nat_unpair, rational_value


class RationalInterval:
    def __init__(self, lo, hi=None, bits=64):
        lo, hi = Fraction(lo), Fraction(lo if hi is None else hi)
        if lo > hi:
            raise ValueError('ordered interval endpoints required')
        self.bits = bits
        scale = 1 << bits
        self.lo = Fraction((lo.numerator * scale) // lo.denominator, scale)
        self.hi = Fraction(-((-hi.numerator * scale) // hi.denominator), scale)

    def _coerce(self, other):
        return other if isinstance(other, RationalInterval) else RationalInterval(other, bits=self.bits)

    def __add__(self, other):
        other = self._coerce(other)
        return RationalInterval(self.lo + other.lo, self.hi + other.hi, self.bits)
    __radd__ = __add__

    def __neg__(self):
        return RationalInterval(-self.hi, -self.lo, self.bits)

    def __sub__(self, other):
        return self + -self._coerce(other)

    def __rsub__(self, other):
        return self._coerce(other) + -self

    def __mul__(self, other):
        other = self._coerce(other)
        products = [a*b for a in (self.lo, self.hi) for b in (other.lo, other.hi)]
        return RationalInterval(min(products), max(products), self.bits)
    __rmul__ = __mul__

    def __truediv__(self, other):
        other = self._coerce(other)
        if other.lo <= 0 <= other.hi:
            raise ZeroDivisionError('interval denominator contains zero')
        return self * RationalInterval(1/other.hi, 1/other.lo, self.bits)

    def mid(self):
        return (self.lo + self.hi)/2

    def rad(self):
        return (self.hi - self.lo)/2

    def contains(self, other):
        other = self._coerce(other)
        return self.lo <= other.lo and other.hi <= self.hi

    def contains_interior(self, other):
        return self.lo < other.lo and other.hi < self.hi

    def magnitude(self):
        return max(abs(self.lo), abs(self.hi))

    def is_zero(self):
        return self.lo == self.hi == 0

    def is_finite(self):
        return True

    def __repr__(self):
        return f'[{self.lo}, {self.hi}]'


def exp_negative(a, bits):
    """Enclose exp(-a), a>=0, using alternating series on [0,1]."""
    a = Fraction(a)
    if a < 0:
        raise ValueError('nonnegative exponential argument required')
    if a >= bits+4:
        # e>2, hence exp(-a)<=2^(-a)<=2^(-bits-4).
        return RationalInterval(0, Fraction(1, 1 << (bits+4)), bits)
    halves = 0
    while a > 1:
        a /= 2
        halves += 1
    work = bits + halves + 8
    threshold = Fraction(1, 1 << work)
    term, total, n = Fraction(1), Fraction(1), 0
    while True:
        following = abs(term)*a/(n+1)
        if following <= threshold:
            lower, upper = ((total-following, total) if n % 2 == 0
                            else (total, total+following))
            result = RationalInterval(lower, upper, work)
            for _ in range(halves):
                result = result * result
            return RationalInterval(max(0, result.lo), min(1, result.hi), bits)
        n += 1
        term *= -a/n
        total += term


def expflat(x):
    bits = x.bits
    if x.hi <= 0:
        return RationalInterval(0, bits=bits), RationalInterval(0, bits=bits)
    upper = exp_negative(1/x.hi, bits).hi
    def damped_square(t):
        # Extra internal bits preserve absolute accuracy after multiplication
        # by t^2, even arbitrarily close to the flat seam.
        value = exp_negative(t, bits+2*t.numerator.bit_length()+4)
        return t*t*value.lo, t*t*value.hi

    if x.lo > 0:
        value = RationalInterval(exp_negative(1/x.lo, bits).lo, upper, bits)
        low_t, high_t = 1/x.hi, 1/x.lo
        ends = [damped_square(low_t), damped_square(high_t)]
        lower, upper_derivative = min(a for a, _ in ends), max(b for _, b in ends)
        if low_t <= 2 <= high_t:
            upper_derivative = max(upper_derivative, damped_square(Fraction(2))[1])
        return value, RationalInterval(lower, upper_derivative, bits)
    # For t>=1/x.hi, t^2 exp(-t) is maximal at max(2,1/x.hi).
    t = max(Fraction(2), 1/x.hi)
    derivative_upper = damped_square(t)[1]
    return RationalInterval(0, upper, bits), RationalInterval(0, derivative_upper, bits)


def step(x):
    if x.hi <= 0:
        return RationalInterval(0, bits=x.bits), RationalInterval(0, bits=x.bits)
    if x.lo >= 1:
        return RationalInterval(1, bits=x.bits), RationalInterval(0, bits=x.bits)
    f, fp = expflat(x)
    g, gp = expflat(1-x)
    denominator = f+g
    # At least one argument >=1/2; e^-2 > 1/16 (e<3).
    denominator = RationalInterval(max(denominator.lo, Fraction(1, 16)), denominator.hi, x.bits)
    return f/denominator, (fp*g+f*gp)/(denominator*denominator)


def evaluate(B, program, time, point):
    bits = time.bits
    zero, one = RationalInterval(0, bits=bits), RationalInterval(1, bits=bits)
    coordinates = [Dual(time, [zero]*4)]
    coordinates += [Dual(y, [one if i == j else zero for j in range(4)])
                    for i, y in enumerate(point)]
    stack = []
    for command in reversed(program):
        tag, payload = nat_unpair(command)
        if tag == 0:
            stack.insert(0, Dual(RationalInterval(rational_value(payload), bits=bits), [zero]*4))
        elif tag == 1:
            stack.insert(0, coordinates[payload] if payload < 5 else Dual(zero, [zero]*4))
        else:
            a, b = (stack + [Dual(zero, [zero]*4)]*2)[:2]
            stack = [a+b if tag == 2 else a*b] + stack[2:]
    P = stack[0] if stack else Dual(zero, [zero]*4)
    cutoffs, slopes = [], []
    lower2, width = Fraction(B*B, 4), Fraction(5*B*B, 16)
    for y in point:
        value, derivative = step((y*y-lower2)/width)
        cutoffs.append(one-value)
        slopes.append(-derivative*(2*y/width))
    cutoff = one
    for value in cutoffs:
        cutoff *= value
    gradient = []
    for j in range(4):
        derivative = slopes[j]
        for i in range(4):
            if i != j:
                derivative *= cutoffs[i]
        gradient.append(cutoff*P.gradient[j] + derivative*P.value)
    return dict(value=cutoff*P.value, gradient=gradient,
                vector_field=[gradient[2], gradient[3], -gradient[0], -gradient[1]])


def named_box(name, bits):
    return RationalInterval(*name.bounds(bits), bits=bits)


def value_gradient(B, program, time, point, goal, progress=None):
    bits, attempts = 64, 0
    while True:
        try:
            result = evaluate(B, program, named_box(time, bits), [named_box(x, bits) for x in point])
            if all(v.rad() <= goal for v in [result['value'], *result['gradient'], *result['vector_field']]):
                return dict(result, bits=bits, refinements=attempts, backend='rational-interval')
        except ArithmeticError:
            pass
        if progress:
            progress(dict(stage='rational value refinement', bits=bits))
        bits *= 2
        attempts += 1


def trajectory(B, program, time, point, goal, progress=None):
    """Actual flow via rational Picard tubes and interval Euler integration.

    On a fixed compact query domain the tube/range extension is locally
    width-Lipschitz. Step error is O(h^2), propagated as (1+C*h)*width;
    arithmetic/input errors vanish with the doubled arbitrary integer precision.
    """
    bits, attempt = 64, 0
    while True:
        duration = named_box(time, bits)
        y = [named_box(x, bits) for x in point]
        count = 1 << (attempt+4)
        h = Fraction(1, count)
        tiny = Fraction(1, 1 << (bits-8))
        good = True

        def field(s, values):
            return [duration*v for v in evaluate(B, program, duration*s, values)['vector_field']]

        for j in range(count):
            tbox = RationalInterval(j*h, (j+1)*h, bits)
            f0 = field(RationalInterval(j*h, bits=bits), y)
            # A uniform positive O(h) margin also covers coordinates with
            # zero initial velocity and a nonzero flat-tail forcing later.
            # Local width consistency makes this first tube sufficient for
            # all sufficiently small h, independently of the 32-try limit.
            margin = 2*h*(1+max(v.magnitude() for v in f0))+tiny
            tube = [RationalInterval(x.lo-margin, x.hi+margin, bits) for x in y]
            for _ in range(32):
                velocity = field(tbox, tube)
                proposal = [x + RationalInterval(0, h, bits)*v for x, v in zip(y, velocity)]
                if all(box.contains_interior(image) for box, image in zip(tube, proposal)):
                    break
                # Keep components that already contain their Picard image.
                # Enlarging those again can amplify a flat-tail forcing in
                # another coordinate faster than its own tube catches up.
                tube = [box if box.contains_interior(image) else
                        RationalInterval(min(box.lo, image.lo)-tiny-(image.hi-image.lo)/4,
                                         max(box.hi, image.hi)+tiny+(image.hi-image.lo)/4, bits)
                        for box, image in zip(tube, proposal)]
            else:
                good = False
                break
            # The strict tube first proves existence inside it. Its Picard
            # image also contains the whole actual path, so reevaluating on
            # that image is rigorous and preserves exact invariant coordinates.
            velocity = field(tbox, proposal)
            y = [x+h*v for x, v in zip(y, velocity)]
            if any(x.rad() > goal for x in y):
                good = False
                break
        if good:
            return dict(endpoint=tuple(y), bits=bits, refinements=attempt, accepted_steps=count,
                        rejected_steps=0, backend='rational-interval',
                        method='validated rational Picard tubes and interval Euler flow')
        if progress:
            progress(dict(stage='rational flow refinement', bits=bits, mesh=count))
        bits *= 2
        attempt += 1
