# /// script
# requires-python = ">=3.12"
# dependencies = ["python-flint==0.9.0", "numpy==2.5.4"]
# ///
"""Fixed k=10, epsilon=0.1 Hamiltonian, analytic flow, and execution checks.

Coordinates are (q1,q2,p1,p2). Source ball i has centre (3i,0,0,0).
H(t,x) takes ambient coordinates; trajectory(t,u,i) takes local |u|<=1.
The analytic flow formula and its verification scope are explained in README.md.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import sys
import time

from flint import arb,ctx

if __package__:
    from ._k10.k10_hamiltonian_adapter import AdaptiveK10Hamiltonian
    from ._k10.hamiltonian_core import norm
else:
    from _k10.k10_hamiltonian_adapter import AdaptiveK10Hamiltonian
    from _k10.hamiltonian_core import norm


def serialize_enclosures(values,accuracy,bits):
    """Check the actual decimal intervals emitted in JSON, after rounding."""
    with ctx.workprec(bits):
        limit=arb(accuracy)
        if not all(x.is_finite() and x.rad()<=limit for x in values):
            raise ArithmeticError('the output intervals do not meet the requested accuracy')
        digits=max(50,bits//3+16)
        for _ in range(4):
            encoded=[x.str(digits) for x in values]
            if all(arb(s).rad()<=limit for s in encoded):return encoded
            digits*=2
        raise ArithmeticError('decimal serialization cannot certify the requested accuracy')


class K10:
    """A single frozen Hamiltonian; precision retries preserve its parameters."""

    k = 10
    epsilon = Fraction(1,10)
    radius = Fraction(73,40)

    def __init__(self,*,bits=512,accuracy='1e-8',max_bits=4096,progress=None):
        if bits<512 or max_bits<bits or not arb(accuracy).is_finite() or not arb(accuracy)>0:
            raise ValueError('need bits>=512, max_bits>=bits and finite positive accuracy')
        ctx.threads=1  # FLINT Python integration callbacks must stay on their owning thread.
        data=json.loads(Path(__file__).with_name('_k10').joinpath('data.json').read_text())
        self.accuracy,self.max_bits=accuracy,max_bits
        self._evaluator=AdaptiveK10Hamiltonian(data['records'],bits=bits,accuracy=accuracy,
            frozen=data['configuration'],quad_workers=1,progress=progress)

    def H(self,t,x):
        """Return an Arb enclosure for the global scalar H(t,x), or raise."""
        return self._evaluator.value(t,x,max_bits=self.max_bits)

    def trajectory(self,t,u,i):
        """Evaluate the prescribed motion; its identification with H's flow is analytic."""
        if type(i) is not int or not 0<=i<10 or len(u)!=4:
            raise ValueError('need a ball index 0..9 and four local coordinates')
        u=[Fraction(str(x)) for x in u]
        if sum(x*x for x in u)>1:
            raise ValueError('the local source point must lie in the closed unit ball')
        if not arb(t).is_finite():
            raise ValueError('finite time required')
        return self._evaluator.trajectory(t,[str(x) for x in u],i,max_bits=self.max_bits)

    def check(self,balls=(0,),*,deep=False,progress=None):
        """Finite execution checks, not a whole-domain correctness certificate.

        Check H along two affine stages of every ball and recompute selected
        embedding centres. The optional deep check evaluates a noncentral
        time-one trajectory.
        No endpoint is accepted solely from the frozen centre table.
        """
        start=time.monotonic();rows=[]
        def record(row):
            rows.append(row)
            if progress:progress(row)
        evaluator=self._evaluator.current
        with ctx.workprec(evaluator.bits):
            radius=arb(73)/40;density=10/radius**4
            if not density>arb('9/10'):
                raise ArithmeticError('the target density is insufficient')
            # Construction also checks each frozen frame's exact Sp(4) identity
            # and its local differential bound. Here exercise the scalar API.
            u=list(map(arb,['1/8','-1/16','1/32','1/64']))
            for i in range(10):
                for t in ['1/16','5/16']:
                    y=evaluator.isotopy(t,u,i)
                    value=evaluator.value(t,y)
                    expected=evaluator.source_generator(t,u,i)
                    if not value.is_finite() or not value.overlaps(expected) or value.rad()>arb(self.accuracy):
                        raise ArithmeticError('the scalar Hamiltonian disagrees with its affine generator')
            record(dict(check='affine_H',balls=10,queries=20,passed=True))
        for i in balls:
            if type(i) is not int or not 0<=i<10:
                raise ValueError('check ball indices must lie in 0..9')
            # Call the real embedding chain even though trajectory(1,0,i)
            # can use the frozen centre enclosure as a shortcut.
            with ctx.workprec(evaluator.bits):
                point,_=evaluator.engine.forward([3*i,0,0,0],i,accuracy=self.accuracy,
                    flow_order=24,guard_bits=0,local_moser=True)
                if not all(x.is_finite() and x.rad()<=arb(self.accuracy) for x in point):
                    raise ArithmeticError('centre recomputation did not reach the requested accuracy')
                if not all(x.overlaps(y) for x,y in zip(point,evaluator.centres[i])):
                    raise ArithmeticError('the recomputed centre disagrees with the frozen parameters')
                if not norm(point)<arb(73)/40:
                    raise ArithmeticError('a recomputed centre was not enclosed in the target')
                record(dict(check='recomputed_centre',ball=i,
                    point=serialize_enclosures(point,self.accuracy,evaluator.bits),passed=True))
        if deep:
            point=self.trajectory('1',['1/8','0','0','0'],0)
            with ctx.workprec(self._evaluator.current.bits):
                if not norm(point)<arb(73)/40:
                    raise ArithmeticError('the noncentral time-one point was not enclosed in the target')
                record(dict(check='noncentral_time_one',ball=0,local_source=['1/8','0','0','0'],
                    point=serialize_enclosures(point,self.accuracy,self._evaluator.current.bits),passed=True))
        return dict(passed=True,k=10,epsilon='1/10',target_radius='73/40',
            scope='finite fixed-instance execution checks; no whole-domain or program-refinement proof',
            density=str(density),checks=rows,seconds=time.monotonic()-start)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true',help='run the small execution check (may take minutes)')
    parser.add_argument('--deep',action='store_true',help='also compute a noncentral time-one trajectory in --check')
    parser.add_argument('--balls',default='0',help='centre recomputation indices for --check')
    parser.add_argument('--time',default='15/16')
    parser.add_argument('--point',nargs=4,default=['0']*4)
    parser.add_argument('--ball',type=int,help='evaluate a source trajectory instead of scalar H')
    parser.add_argument('--bits',type=int,default=512)
    parser.add_argument('--max-bits',type=int,default=4096)
    parser.add_argument('--accuracy',default='1e-8')
    parser.add_argument('--progress',action='store_true',help='print numerical stages and refinement progress to stderr')
    args=parser.parse_args();start=time.monotonic()
    if args.deep and not args.check:parser.error('--deep requires --check')
    def progress(stage,details):
        print(stage,json.dumps(details,default=str) if isinstance(details,dict) else '',file=sys.stderr,flush=True)
    example=K10(bits=args.bits,max_bits=args.max_bits,accuracy=args.accuracy,
                progress=progress if args.progress else None)
    if args.check:
        result=example.check(tuple(map(int,args.balls.split(','))),deep=args.deep,
            progress=lambda row:print(json.dumps(row),file=sys.stderr,flush=True))
    else:
        value=[example.H(args.time,args.point)] if args.ball is None else example.trajectory(args.time,args.point,args.ball)
        result=dict(k=10,epsilon='1/10',time=args.time,input=args.point,ball=args.ball,
            value=serialize_enclosures(value,args.accuracy,example._evaluator.current.bits),accuracy=args.accuracy,
            scope='scalar H enclosure' if args.ball is None else 'prescribed trajectory enclosure',
            seconds=time.monotonic()-start)
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
