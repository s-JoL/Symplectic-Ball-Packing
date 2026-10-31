# /// script
# requires-python = ">=3.12"
# dependencies = ["python-flint==0.9.0"]
# ///
"""Uniform proof-backed packing for k>=10, 0<epsilon<1, without a runtime bound.

Grouped ambient coordinates: q1,q2,p1,p2. CLI scalars are exact rational
strings. The library also accepts callable refining real names.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys

from flint import arb, ctx

if __package__:
    from ._packing import compile_packing
else:
    from _packing import compile_packing


def serialize_enclosures(values, tolerance, bits):
    """Preserve both containment and the requested radius in emitted JSON."""
    if values and hasattr(values[0], 'lo'):
        goal = Fraction(tolerance)
        if not all(v.rad() <= goal for v in values):
            raise ArithmeticError('rational output failed the requested radius')
        return [dict(lower=str(v.lo), upper=str(v.hi)) for v in values]
    with ctx.workprec(bits):
        from flint import fmpq
        goal = Fraction(tolerance)
        limit = arb(fmpq(goal.numerator, goal.denominator))
        if not all(v.is_finite() and v.rad() < limit for v in values):
            raise ArithmeticError('no room to serialize the requested error bound')
        digits = max(50, bits // 3 + 16)
        while True:
            result = [v.str(digits) for v in values]
            if all(arb(s).contains(v) and arb(s).rad() <= limit for s, v in zip(result, values)):
                return result
            digits *= 2


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--k', type=int, required=True)
    parser.add_argument('--epsilon', required=True)
    parser.add_argument('--query', choices=('describe', 'value-gradient', 'flow'), default='describe')
    parser.add_argument('--time', default='1')
    parser.add_argument('--point', nargs=4, default=['0'] * 4)
    parser.add_argument('--accuracy', default='1e-8')
    parser.add_argument('--bits', type=int, default=256)
    parser.add_argument('--backend', choices=('auto', 'rational'), default='auto')
    parser.add_argument('--run-directory', type=Path)
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    goal = Fraction(args.accuracy)
    if goal <= 0:
        parser.error('--accuracy must be positive')
    progress = lambda row: print(json.dumps(row), file=sys.stderr, flush=True)
    H = compile_packing(args.k, args.epsilon, run_directory=args.run_directory, progress=progress)
    report = H.description()
    if args.query == 'value-gradient':
        result = H.value_gradient(args.time, args.point, tolerance=goal / 4,
                                  initial_bits=args.bits, progress=progress, backend=args.backend)
        encoded = serialize_enclosures([result['value'], *result['gradient'], *result['vector_field']],
                                       goal, result['bits'])
        report['query'] = dict(kind=args.query, time=args.time, point=args.point,
                              accuracy=str(goal), value=encoded[0], gradient=encoded[1:5],
                              vector_field=encoded[5:], bits=result['bits'])
    elif args.query == 'flow':
        result = H.trajectory(args.time, args.point, tolerance=goal / 4,
                              initial_bits=args.bits, progress=progress, backend=args.backend)
        report['query'] = dict(kind=args.query, time=args.time, point=args.point,
                              accuracy=str(goal), endpoint=serialize_enclosures(
                                  result['endpoint'], goal, result['bits']),
                              bits=result['bits'], accepted_steps=result['accepted_steps'])
    data = json.dumps(report, indent=2) + '\n'
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(data)
    print(data, end='')


if __name__ == '__main__':
    main()
