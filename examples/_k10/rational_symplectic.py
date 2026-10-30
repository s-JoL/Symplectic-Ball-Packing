"""Fixed-frame differential bound; no parameter search or projection."""
from flint import arb,arb_mat


def variation_bound(matrix,derivative_box):
    A=arb_mat([[arb(matrix[i,j]) for j in range(4)] for i in range(4)])
    D=arb_mat(derivative_box)
    I=arb_mat([[int(i==j) for j in range(4)] for i in range(4)])
    E=A.inv()*D-I
    return sum(abs(E[i,j]).upper()**2 for i in range(4) for j in range(4)).sqrt().upper()
