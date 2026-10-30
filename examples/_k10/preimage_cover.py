"""Finite interval covers proving exclusion from the compact cutoff image.

This is the slow fallback for a point where a reverse chart is unresolved.
No failed solve excludes a box: it forces subdivision. A completed cover
alone proves absence. The construction can be advanced in bounded batches
while a reverse calculation is retried independently.
"""
from flint import arb,ctx


class CutoffImageCover:
    def __init__(self,evaluator,point,index,radius='10001/10000'):
        self.evaluator,self.index=evaluator,index
        with ctx.workprec(evaluator.bits):
            self.point=list(map(arb,point));self.radius=arb(radius)
            r=self.radius.upper()
            self.pending=[tuple([(-r,r)]*4)]
            self.examined=self.excluded=0

    @staticmethod
    def box(edges):
        return [arb((a+b)/2,(b-a)/2) for a,b in edges]

    def advance(self,budget=16):
        C=self.evaluator
        with ctx.workprec(C.bits):
            for _ in range(budget):
                if not self.pending:return True
                edges=self.pending.pop();box=self.box(edges);self.examined+=1
                norm_lower=sum((arb(0) if x.contains(0) else min(abs(x.lower()),abs(x.upper())))**2 for x in box)
                if norm_lower.lower()>self.radius.upper()*self.radius.upper():
                    self.excluded+=1;continue
                try:
                    original=[x+(3*self.index if j==0 else 0) for j,x in enumerate(box)]
                    value,_=C.forward(original,self.index,accuracy='1',neighbourhood=True,range_only=True)
                    if any(not a.overlaps(b) for a,b in zip(value,self.point)):
                        self.excluded+=1;continue
                except (ArithmeticError,ValueError,ZeroDivisionError):
                    pass
                coordinate=max(range(4),key=lambda j:(edges[j][1]-edges[j][0]).mid())
                left,right=edges[coordinate];middle=((left+right)/2).mid()
                if not left<middle or not middle<right:
                    # Restore the unresolved box: exhausting precision is
                    # not evidence for its exclusion.
                    self.pending.append(edges)
                    raise ArithmeticError('increase precision for the exclusion cover')
                a,b=list(edges),list(edges)
                a[coordinate]=(left,middle);b[coordinate]=(middle,right)
                self.pending.extend([tuple(a),tuple(b)])
            return not self.pending
