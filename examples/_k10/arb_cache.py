"""Exact dyadic identities for interval memoization.

Formatted Arb decimal strings enclose their values but are not injective.
They may serialize an enclosure, but must not identify a cached input.
"""
from flint import arb


def floor_mid(value):
    """Exact integer choice even arbitrarily close to a lattice seam."""
    return int(value.mid().floor().unique_fmpz())


def nearest_mid(value):
    return floor_mid(value.mid()+arb(1)/2)


def ball_key(value):
    return tuple((str(part.man_exp()[0]),int(part.man_exp()[1]))
                 for part in (value.mid(),value.rad()))


def root_precision(bits,goal):
    """Choose an internal budget; final output intervals decide acceptance."""
    goal=arb(goal)
    if not goal.is_finite() or not goal>0:raise ValueError('positive finite accuracy required')
    m,e=goal.lower().man_exp()
    exponent=int(m).bit_length()-1+int(e)
    return min(bits-32,max(64,bits//8,64-exponent))
