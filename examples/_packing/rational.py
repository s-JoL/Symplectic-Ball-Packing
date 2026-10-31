"""Outward-rounded conversion of exact rational input."""
from fractions import Fraction
from flint import arb, fmpq

def rational(value):
    value = Fraction(value)
    return arb(fmpq(value.numerator, value.denominator))
