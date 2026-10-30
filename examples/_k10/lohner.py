"""Lohner change of basis with interval Peano-Baker transition bounds.

QR chooses a numerical basis only. Its inverse and every propagated error
are computed with Arb; orthogonality of the stored float basis is never
assumed. The matrix bound is valid for a time-varying interval Jacobian.
"""
import math

from flint import arb, arb_mat


def identity(n):
    return arb_mat([[int(i == j) for j in range(n)] for i in range(n)])


def _weighted_bound(M):
    """A verified induced norm after a positive diagonal basis change.

    Floating balancing only chooses weights. All actual norm inequalities
    are evaluated afresh with Arb, so no spectral approximation is used
    as a bound. This prevents a large one-way shear from dictating h.
    """
    import numpy as np
    n=M.nrows()
    B=[[abs(M[i,j]).upper() for j in range(n)] for i in range(n)]
    weights=np.ones(n)
    values=np.array([[float(x) for x in row] for row in B])
    if np.all(np.isfinite(values)):
        for _ in range(12):
            candidate=np.maximum(values@weights,1e-100)
            updated=np.sqrt(weights)*np.sqrt(candidate)
            updated/=max(updated)
            weights=np.maximum(updated,1e-80)
    d=list(map(arb,weights.tolist()))
    L=max(sum(B[i][j]*d[j]/d[i] for j in range(n)) for i in range(n)).upper()
    original=max(sum(row) for row in B).upper()
    return (d,L) if L<original else ([arb(1)]*n,original)


def transition(jacobian, step, order=20,weighted=False):
    n = jacobian.nrows()
    weights,L = (_weighted_bound(jacobian) if weighted else ([arb(1)]*n,
        max(sum(abs(jacobian[i,j]).upper() for j in range(n)) for i in range(n)).upper()))
    a = step*L
    if not a.is_finite() or a > 1:
        return None
    term, result = identity(n), identity(n)
    for k in range(1, order+1):
        term = (term*jacobian)*(step/k)
        result += term
    tail = (a.exp()*a**(order+1)/math.factorial(order+1)).upper()
    for i in range(n):
        for j in range(n):
            result[i, j] += arb(0, (tail*weights[i]/weights[j]).upper())
    return result


def triangular_transition(jacobian, step, split, order=20,weighted=False):
    """Peano--Baker enclosure for [[A,0],[B,C]].

    A large B in a variational equation does not require a small time
    step: every product contains at most one B. The scalar majorant
    [[L,0],[K,L]] bounds products of arbitrary time-varying matrices,
    including noncommuting A and C.
    """
    n = jacobian.nrows()
    if any(not jacobian[i,j].is_zero() for i in range(split) for j in range(split,n)):
        raise ValueError('transition matrix does not have the stated triangular blocks')
    A=arb_mat([[jacobian[i,j] for j in range(split)] for i in range(split)])
    C=arb_mat([[jacobian[i,j] for j in range(split,n)] for i in range(split,n)])
    wa,La=(_weighted_bound(A) if weighted else ([arb(1)]*split,
        max(sum(abs(A[i,j]).upper() for j in range(split)) for i in range(split)).upper()))
    size=n-split
    wc,Lc=(_weighted_bound(C) if weighted else ([arb(1)]*size,
        max(sum(abs(C[i,j]).upper() for j in range(size)) for i in range(size)).upper()))
    weights=wa+wc;L=max(La,Lc)
    K=max(sum(abs(jacobian[i,j]).upper()*weights[j]/weights[i] for j in range(split))
          for i in range(split,n)).upper()
    a, b = step*L, step*K
    if not a.is_finite() or not b.is_finite() or a > 1:
        return None
    term, result = identity(n), identity(n)
    for k in range(1,order+1):
        term = (term*jacobian)*(step/k)
        result += term
    diagonal_tail = (a.exp()*a**(order+1)/math.factorial(order+1)).upper()
    lower_tail = (a.exp()*b*a**order/math.factorial(order)).upper()
    for i in range(n):
        for j in range(n):
            if i < split and j >= split:
                continue
            tail=lower_tail if i>=split and j<split else diagonal_tail
            result[i,j] += arb(0,(tail*weights[i]/weights[j]).upper())
    return result


def propagate(centre_result, basis, radii, M,blocks=None):
    import numpy as np
    n = len(radii)
    predicted = M*basis
    mid = np.array([[float(predicted[i, j].mid()) for j in range(n)] for i in range(n)])
    if blocks is None:
        Q, _ = np.linalg.qr(mid)
    else:
        # Preserve the triangular structure of first variations. A large
        # physical-to-derivative shear must not rotate physical errors into
        # arbitrary combinations of all derivative columns.
        if sorted(i for group in blocks for i in group)!=list(range(n)):
            raise ValueError('Lohner blocks must partition the state coordinates')
        Q=np.zeros((n,n))
        for group in blocks:
            block,_=np.linalg.qr(mid[np.ix_(group,group)])
            Q[np.ix_(group,group)]=block
    new_basis = arb_mat(Q.tolist())
    inverse = new_basis.inv()
    T = inverse*M*basis
    error = arb_mat([[value-value.mid()] for value in centre_result])
    transported = T*arb_mat([[arb(0, r)] for r in radii])+inverse*error
    new_radii = [abs(transported[i, 0]).upper() for i in range(n)]
    midpoint = [value.mid() for value in centre_result]
    box = new_basis*arb_mat([[arb(0, r)] for r in new_radii])
    endpoint = [midpoint[i]+box[i, 0] for i in range(n)]
    if not all(x.is_finite() for x in endpoint):
        raise ArithmeticError('Lohner basis change was not certified invertible')
    return endpoint, new_basis, new_radii
