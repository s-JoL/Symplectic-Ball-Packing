"""Point evaluation and real flows of a finite global Hamiltonian.

A scalar name supplies rational q(p) with |q(p)-x| <= 2**(-p).
Names must describe the same real throughout; finite queries cannot verify
that promise. Disjoint successive enclosures are rejected. Intrinsic-width
input balls are never silently converted into point names.
"""
from fractions import Fraction
import sys

from flint import arb, ctx

from .rational import rational
from .polynomial import FinitePolynomialHamiltonian
from .flow import integrate

# Finite exact input/output codes have no decimal-length bound in M2.
if hasattr(sys, 'set_int_max_str_digits'):
    sys.set_int_max_str_digits(0)


def exact_fraction(value):
    if isinstance(value, arb):
        if not value.is_finite() or not value.is_exact():
            raise ValueError('a point requires an exact scalar or a refining real name')
        m, e = map(int, value.man_exp())
        return Fraction(m*(1 << e)) if e >= 0 else Fraction(m, 1 << -e)
    try:
        return Fraction(value)
    except (TypeError, ValueError, OverflowError) as error:
        raise ValueError('a finite rational approximation is required') from error


class ScalarName:
    def __init__(self, value):
        self.oracle = value if callable(value) else None
        self.exact = None if self.oracle else exact_fraction(value)
        self.previous = None

    def bounds(self, precision):
        if not isinstance(precision, int) or precision < 0:
            raise ValueError('nonnegative name precision required')
        if self.oracle is None:
            return self.exact, self.exact
        q = exact_fraction(self.oracle(precision)); error = Fraction(1, 1 << precision)
        lo, hi = q-error, q+error
        if self.previous is not None:
            lo, hi = max(lo, self.previous[0]), min(hi, self.previous[1])
            if lo > hi:
                raise ValueError('successive scalar-name enclosures are disjoint')
        self.previous = lo, hi
        return lo, hi

    def enclosure(self, precision):
        lo, hi = self.bounds(precision)
        return rational((lo+hi)/2)+arb(0, rational((hi-lo)/2).upper())


def lower_epsilon(epsilon):
    """Find a positive rational below an arbitrary valid epsilon in (0,1)."""
    name = ScalarName(epsilon)
    if name.oracle is None:
        if not 0 < name.exact < 1:
            raise ValueError('epsilon must lie strictly between zero and one')
        return name.exact, dict(kind='exact-rational', epsilon=str(name.exact))
    precision = 128
    while True:
        lo, hi = name.bounds(precision)
        if 0 < lo and hi < 1:
            return lo, dict(kind='refining-real-name', precision=precision,
                            lower=str(lo), upper=str(hi), radius_contract='2^-p')
        precision *= 2


class NamedFiniteHamiltonian:
    def __init__(self, B, program):
        self.field = FinitePolynomialHamiltonian(B, program)

    @staticmethod
    def _inputs(time, point, tolerance, initial_bits):
        if len(point) != 4:
            raise ValueError('four grouped phase coordinates required')
        goal = exact_fraction(tolerance)
        if goal <= 0:
            raise ValueError('positive rational accuracy required')
        if not isinstance(initial_bits, int) or initial_bits < 32:
            raise ValueError('initial precision must be an integer at least32')
        return ScalarName(time), [ScalarName(x) for x in point], goal

    def value_gradient(self, time, point, *, tolerance='1e-8', initial_bits=256, progress=None, backend='auto'):
        time, point, goal = self._inputs(time, point, tolerance, initial_bits)
        if backend not in ('auto', 'rational'):
            raise ValueError('backend must be auto or rational')
        bits = initial_bits; refinements = 0
        while True:
            if backend == 'rational' or bits >= 2**31:
                from .exact import value_gradient
                return value_gradient(self.field.B, self.field.program, time, point, goal, progress)
            try:
                with ctx.workprec(bits):
                    t = time.enclosure(bits); y = [x.enclosure(bits) for x in point]
                    try:
                        result = self.field.evaluate(t, y, bits=bits)
                        values = [result['value'], *result['gradient'], *result['vector_field']]
                        if all(v.is_finite() and v.rad() <= rational(goal) for v in values):
                            return dict(result, bits=bits, refinements=refinements)
                    except OverflowError:
                        backend = 'rational'
                    except (ArithmeticError, ZeroDivisionError):
                        pass
            except OverflowError:
                backend = 'rational'
                continue
            if progress:
                progress(dict(stage='finite Hamiltonian real-name refinement', bits=bits))
            bits *= 2; refinements += 1

    def trajectory(self, time, point, *, tolerance='1e-8', initial_bits=256, order=8, progress=None, backend='auto'):
        """Enclose the actual ambient trajectory at any named real time.

        Integrate dY/ds = t*X_H(t*s,Y), s in [0,1]. The named parameter t
        may be positive, negative, or zero. No finite retry/step cap is
        imposed globally: precision, mesh, and per-attempt budget refine.
        """
        time, point, goal = self._inputs(time, point, tolerance, initial_bits)
        if backend not in ('auto', 'rational'):
            raise ValueError('backend must be auto or rational')
        if not isinstance(order, int) or order < 2:
            raise ValueError('a finite Taylor order of at least two is required')
        bits = initial_bits; attempt = 0; failures = []
        while True:
            if backend == 'rational' or bits >= 2**31 or order >= 2**31:
                from .exact import trajectory
                return trajectory(self.field.B, self.field.program, time, point, goal, progress)
            try:
                with ctx.workprec(bits):
                    duration = time.enclosure(bits); initial = [x.enclosure(bits) for x in point]
                    step = Fraction(1, 1 << (attempt+4))

                    def vector_field(s, y):
                        return [duration*v for v in self.field.jet(duration*s, y)['vector_field']]

                    try:
                        result = integrate(vector_field, initial, bits=bits, order=order,
                            max_step=rational(step), max_radius=rational(goal),
                            max_steps=1 << (2*attempt+14), remainder_guard_bits=8, progress=progress)
                        if not all(v.is_finite() and v.rad() <= rational(goal) for v in result.endpoint):
                            raise ArithmeticError('actual flow endpoint failed the original accuracy gate')
                        return dict(endpoint=result.endpoint, bits=bits, refinements=attempt,
                            accepted_steps=result.accepted_steps, rejected_steps=result.rejected_steps,
                            order=order, max_step=str(step), failed_attempts=failures,
                            method='validated actual global Hamiltonian flow with refining real parameters')
                    except (ArithmeticError, ZeroDivisionError, OverflowError) as error:
                        if isinstance(error, OverflowError):
                            backend = 'rational'
                        failures.append(dict(bits=bits, max_step=str(step), error=str(error)))
                        if progress:
                            progress(dict(stage='finite Hamiltonian flow refinement', **failures[-1]))
            except OverflowError:
                backend = 'rational'
                continue
            bits *= 2; attempt += 1
