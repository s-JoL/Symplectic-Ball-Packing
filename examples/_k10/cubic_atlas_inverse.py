"""Certified inverse on a projective atlas, independent of wp branch cuts.

Choose nonzero denominator Z_d and unused coordinate Z_k. The remaining
ratio Z_i/Z_d is a local coordinate of the Fermat curve. The other ratio
is one of three cube roots; disjoint rotated enclosures identify its
branch. A dense torus grid supplies guesses only, never a certificate.
"""
import heapq
from flint import arb,acb,ctx


def _root(C,data,target,centre,radius):
    centre=acb(centre).mid();radius=arb(radius)
    value,slope,_=data(centre);slope=slope.mid()
    if not slope.is_finite() or slope.contains(0):raise ArithmeticError('unresolved atlas derivative')
    box=centre+acb(arb(0,radius),arb(0,radius))
    _,derivative,_=data(box)
    kappa=abs(1-derivative/slope).upper()
    residual=abs((target-value)/slope).upper()
    if not kappa<arb(1)/2 or not residual+kappa*radius<radius:
        raise ArithmeticError('atlas inverse contraction was not certified')
    error=radius
    for _ in range(max(32,C.bits)):
        box=centre+acb(arb(0,error),arb(0,error))
        _,derivative,_=data(box);value,_,_=data(centre)
        kappa=abs(1-derivative/slope).upper()
        if not kappa<1:raise ArithmeticError('atlas inverse lost its derivative bound')
        correction=(target-value)/slope
        bound=(abs(correction).upper()/(1-kappa)).upper()
        if bound<arb(2)**(-C.bits//2):
            return centre+acb(arb(0,bound),arb(0,bound))
        if not bound<error:break
        next_centre=(centre+correction).mid()
        shifted=(abs(centre-next_centre).upper()+bound).upper()
        if shifted<error:centre,error=next_centre,shifted
        else:error=bound
    return centre+acb(arb(0,error),arb(0,error))


def atlas_inverse(C,Z,*,seeds=(),grid=None):
    """Return a verified complex torus representative of a Fermat point.

    The exact point represented by Z must lie on the Fermat cubic.
    A failed finite search is explicit; the grid grows on precision retry.
    """
    with ctx.workprec(C.bits):
        d=max(range(3),key=lambda j:abs(Z[j]).lower())
        if Z[d].contains(0):raise ArithmeticError('refine the projective inverse denominator')
        k=max((j for j in range(3) if j!=d),key=lambda j:abs(Z[j]).lower())
        if Z[k].contains(0):raise ArithmeticError('refine the second nonzero Fermat coordinate')
        i=next(j for j in range(3) if j not in (d,k))
        target,other=Z[i]/Z[d],Z[k]/Z[d]
        def data(z):
            if z.real.rad().is_zero() and z.imag.rad().is_zero():raw,D=C._raw(z)
            else:raw,D,_=C._taylor_box(z)
            denominator=raw[d]
            return raw[i]/denominator,(D[i]*denominator-raw[i]*D[d])/(denominator*denominator),raw
        def certify(seed,radius):
            root=_root(C,data,target,seed,radius)
            _,_,raw=data(root);branch=raw[k]/raw[d]
            if not branch.is_finite() or not branch.overlaps(other):
                raise ArithmeticError('atlas root belongs to another Fermat branch')
            if (branch*C.tau).overlaps(other) or (branch*C.tau*C.tau).overlaps(other):
                raise ArithmeticError('refine the three Fermat cube-root branches')
            return root
        for seed in seeds:
            try:return certify(seed,arb(1)/1024)
            except (ArithmeticError,ValueError,ZeroDivisionError):pass
        N=2**max(3,C.bits.bit_length()-4) if grid is None else grid
        if not isinstance(N,int) or N<2:raise ValueError('the atlas grid must have at least two divisions')
        # Order guesses by both projective ratios, so a different sheet of
        # the first projection does not crowd out the correct local chart.
        candidates=[]
        for a in range(N):
            for b in range(N):
                seed=(acb(arb(a)/N)+C.tau*(arb(b)/N)).mid()
                raw,_=C._raw(seed)
                if raw[d].contains(0):continue
                score=abs(raw[i]/raw[d]-target).upper()+abs(raw[k]/raw[d]-other).upper()
                if score.is_finite():candidates.append((score.upper(),a,b,seed))
        for _,_,_,seed in heapq.nsmallest(64,candidates,key=lambda row:row[:3]):
            for radius in [arb(1)/1024,arb(2)/N]:
                try:return certify(seed,radius)
                except (ArithmeticError,ValueError,ZeroDivisionError):pass
        raise ArithmeticError(f'projective inverse atlas needs a finer grid than {N}')
