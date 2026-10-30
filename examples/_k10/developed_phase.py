"""Real developed cubic phase on the K10 Landau image.

The infinite Jacobi product is evaluated with a geometric logarithm tail.
Only factors in the closed right half-plane use principal arguments. The
phase of the original theta section is never reduced modulo an integer.
An overall additive constant is deliberately omitted: normalization of the
embedding action cancels it exactly.
"""
import math
from .arb_cache import floor_mid,nearest_mid
from flint import arb, acb, ctx


def product_phase(C,s,y,strip=None):
    """Phase of exp(-2pi*i*w) prod_j theta1(w-zero_j)."""
    with ctx.workprec(C.bits):
        w=acb(s)+C.tau*y
        zeros=[acb(0),(2+C.tau)/3,(1+2*C.tau)/3]
        q=(acb(0,2*C.pi)*C.tau).exp()
        r=abs(q).upper()
        count=max(12,math.ceil((C.bits+32)/7))
        constant=C.tau.real/8
        qn=q
        for n in range(1,count+1):
            constant+=(1-qn).arg()/(2*C.pi)
            qn*=q
        out=-w.real+3*constant
        tail=3*r**(count+1)/((1-r)*(1-r**(count+1)))
        for k,zero in enumerate(zeros):
            xi=w-zero
            values=[]
            for sign in (1,-1):
                if strip is not None and sign != (1 if strip>=k else -1):continue
                if sign==1 and xi.imag.upper()<0 or sign==-1 and xi.imag.lower()>0:continue
                small=(acb(0,2*C.pi*sign)*xi).exp()
                factor=1-small
                if factor.contains(0):
                    raise ArithmeticError('developed phase box meets a cubic divisor')
                values.append(sign*(arb(1)/4-xi.real/2)+factor.arg()/(2*C.pi))
            value=values[0]
            for v in values[1:]:value=value.union(v)
            out+=value
            plus=(acb(0,2*C.pi)*xi).exp()
            minus=(acb(0,-2*C.pi)*xi).exp()
            qn=q
            for n in range(1,count+1):
                out+=((1-qn*plus).arg()+(1-qn*minus).arg())/(2*C.pi)
                qn*=q
            magnitude=max(abs(plus).upper(),abs(minus).upper())
            first=r**(count+1)*magnitude
            if not first < 1:raise ArithmeticError('increase the Jacobi product length')
            tail+=r**(count+1)*(abs(plus)+abs(minus))/((1-r)*(1-first))
        return out+arb(0,(tail/(2*C.pi)).upper())


def landau_phase(bridge,U,V,*,old=None,vertical_sheet=0):
    """A continuous phase lift on the specific K10 source image.

    At each marked V row, the K10 shear has a zero collar and U lies in
    its original cell (0,1). Subtracting j removes the integer jump of
    the sine development there. Outside those collars, the exact integer
    horizontal period 3*y-j-1/2 retains every shear winding.
    """
    with ctx.workprec(bridge.bits):
        U,V=arb(U),arb(V)
        if not V > 0 or not V < 1:
            raise ValueError('K10 phase chart requires 0<V<1')
        u,y=bridge.inverse_base(U,V) if old is None else old
        n=floor_mid(U)
        x=u+y-n
        results=[]
        for j in range(3):
            left,right=arb(j)/3,arb(j+1)/3
            if y.upper()<left or y.lower()>right:continue
            # Split only the chart decision. Correlation loss enlarges the
            # enclosure, without changing the value being enclosed.
            lo,hi=max(y.lower(),left.lower()),min(y.upper(),right.upper())
            yc=arb((lo+hi)/2,(hi-lo)/2)
            if n!=vertical_sheet and (abs(yc-left).contains(0) or abs(yc-right).contains(0)):
                raise ArithmeticError('refine a phase box at a marked row outside the zero-shear cell')
            s=x-yc
            raw=product_phase(bridge.cubic,s,yc,strip=j)
            A=raw+3*s*yc-arb(3)/4*yc*yc-yc/2
            results.append(A-j+n*(3*yc-j-arb(1)/2)+vertical_sheet*j-bridge.G(u+y,y))
        if not results:raise ArithmeticError('no developed phase chart')
        result=results[0]
        for value in results[1:]:result=result.union(value)
        return result
