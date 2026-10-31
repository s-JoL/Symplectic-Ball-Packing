# Executable programs

For **all `k>=10`, `0<epsilon<1`**, use [`packing.py`](packing.py).
The [uniform program guide](PACKING.md) gives the full proof contract, runtime
entry points and independent verification commands. Compilation is a terminating
reference search without a practical time or resource bound.

The remainder of this page documents the separate fixed-input implementation.

## Fixed k=10, epsilon=0.1 executable program

[`k10.py`](k10.py) implements the fixed-input construction: one scalar global
Hamiltonian `H(t,x)` and its analytically parametrized motion of ten closed unit
balls centred at `(3i,0,0,0)`, `i=0,…,9`. Coordinates are `(q1,q2,p1,p2)`.
The target radius is `73/40`, with volume fraction
`10/(73/40)^4 = 25600000/28398241 > 9/10`.

This is a native fixed-input program alongside the mathematical construction
on main. It is not a full Epoch AI submission: general inputs, the required
single-file/PyTorch differentiation interface, performance limits and official
acceptance are outside this fixed-input example. General inputs are implemented
by the separate uniform program above. Both are subsequent to the archived v1.0.1
publication.

## Run

From the repository root, `uv` reads the script's pinned dependencies:

```sh
uv run examples/k10.py --check
uv run examples/k10.py --check --deep --progress
uv run examples/k10.py --time 15/16 --point 0 0 0 0
uv run examples/k10.py --time 1 --ball 0 --point 1/8 0 0 0 --progress
```

Alternatively install `python-flint==0.9.0` and `numpy==2.5.4` in Python 3.12+
and run `python examples/k10.py …`. No other worktree or run cache is needed.
Nonlinear queries can take minutes. `--progress` reports stages to stderr;
the result is JSON on stdout. `--max-bits` limits precision retries, and an
unresolved computation raises instead of returning an unverified midpoint.

`H` takes ambient coordinates. With `--ball i`, `--point` is the local source
coordinate `u`, so the initial point is `(3i,0,0,0)+u`. Source coordinates are
interpreted as exact decimal/rational values and checked against `|u|≤1`.
Returned numbers are Arb enclosures; even after JSON decimal serialization,
each coordinate's radius must meet `--accuracy` (default `1e-8`).

The essential scalar/interval kernels are in `_k10/`; `data.json` holds the
fixed parameters, exact rational frames and local differential enclosures.
The implementation is specified by the included [common Hamiltonian](
_k10/hamiltonian_core.py), [tail matching](_k10/tail_matching.py) and the
fixed parameters in [data.json](_k10/data.json). Only the two pinned numerical
dependencies are required.

## Cubic normalization

The infinite theta lift and its deck identities are given in the
[Fermat torus construction](../paper/supp/cubic-bundle.tex); the normal and
return flows are given in [the return construction](../paper/supp/cubic-return.tex).
The scalar bridge uses coordinates `x=u+v, y=v`, and writes the connection as
`eta=A dx+B dy`, where `A=eta_u` and `B=eta_v-eta_u`.

The exact constants in `direct_cubic_bridge.py` come from symmetry, rather
than rounded integrals. On the real axis, all theta coefficients have the
common phase `exp(-i*pi/8)` up to real signs. The homogeneous lift therefore
has zero imaginary Hermitian connection in that direction, so
`eta_u(u,0)=0` and `H(0)=integral_0^1 A(x,0) dx=0`.

On `(u,v)=(-y,y)`, conjugation and multiplication by `1+tau` identify the
Weierstrass representatives. The Weierstrass vector has zero imaginary
connection along this line. The sigma-theta relation with full quasiperiod
`eta_1=pi/Im(tau)` gives `d arg(T)/dy=3*pi*y`; the factor `T^3` contributes
`9*y/2` to the connection. The implemented unit-lift gauge
`exp(i*pi*(6*u*v-3*v^2/2-v))` contributes `-15*y/2-1/2`. Consequently

```text
B(0,y)=-3*y-1/2,
G(0,y)=integral_0^y B(0,s) ds=-3*y^2/2-y/2,
G(0,1)=-2.
```

These identities extend across theta zeros by smoothness of the nonvanishing
homogeneous lift. They fix `H0=0`, `G01=-2` and `vertical_G` exactly. Regression
tests also check the connection identities at independently evaluated points;
the tests are not a substitute for the symmetry argument.

## Why the trajectory is the Hamiltonian flow

Write `f_i` for the implemented symplectic embedding and `S_i` for its normalized
primitive, with `dS_i=f_i*lambda-lambda`, `S_i(0)=0` and
`lambda_x(w)=omega(x,w)/2`. The embedding/layer/primitive identities follow the
[main construction](../paper/main/hamiltonian.tex) and its explicit cubic and
normal-transfer formulas. This example uses a nearby exact rational symplectic
frame `A_i`, rather than requiring an exactly stored derivative.

The constructor checks `A_i^T Omega A_i=Omega` exactly and, from the stored
full local differential box, checks

```text
||A_i^-1 Df_i-I|| ≤ eta_i < 1/40002,
r1=20001/20000 < r2=10001/10000 < r3=20003/20000 < r4=5001/5000,
tau*r3 ≤ local_radius_i.
```

For `|u|≤1`, let `G_i(w)=A_i^-1(f_i(tau*w)-f_i(0))/tau`.
Then `T(w)=u+w-G_i(w)` is a contraction of the closed `r1` ball into itself.
Its unique fixed point is

```text
nu_i(u)=f_i^-1(f_i(0)+tau*A_i*u)/tau,
|nu_i(u)|≤1/(1-eta_i)<r1.
```

The program computes this inverse locally using forward evaluations. If `w`
is an exact iterate, `T(w)` is enclosed by an interval calculation and the
fixed point lies within `eta_i*|T(w)-w|/(1-eta_i)` of `T(w)`. This a posteriori
bound, plus the final output-radius check, decides acceptance. A sufficiently
tight inverse of the stored differential box is a cheaper initial enclosure.

The first five stages translate the separated balls to `f_i(0)/tau+u`;
the sixth follows a symplectic linear path to `f_i(0)/tau+A_i*u`.
The seventh stage is constant. In the final stage put

```text
v(t)=tau+(1-tau)*step(8t-7),
F_i,t(xi)=f_i(v(t)*xi)/v(t),
z_i(t,u)=F_i,t(nu_i(u)),
h_i,t(xi)=-2*v'(t)*S_i(v(t)*xi)/v(t)^3.
```

The defining label identity makes this agree exactly with the affine stage at
`v=tau`. Flat clocks make the joins smooth. Differentiating the primitive
identity gives `F_i,t* (i_(partial_t F_i,t) omega)=d h_i,t`. Thus, with the
convention `i_X omega=dH`, the pushed-forward scalar generator has
`X_H=(H_p,-H_q)=partial_t z_i` on these trajectories.

The ambient program sums the chart generators composed with their inverse
charts and the smooth cutoff `1-step((|xi|²-r1²)/(r2²-r1²))`. The charts are
disjoint; the cutoff is one near every source trajectory and zero before the
chart boundary. It therefore defines one smooth global Hamiltonian with
compact spatial support. Uniqueness of its flow identifies

```text
Phi_H^1((3i,0,0,0)+u)=f_i(nu_i(u)),  |u|≤1.
```

These endpoints belong to the disjoint enlarged embedding containers in the
target ball. Symplectic volume preservation gives the density above.
The trajectory command evaluates this formula; a second numerical integration
of the ambient scalar `H` is not how the flow is defined or computed.

## Verification scope

`--check` evaluates 20 affine Hamiltonian queries across all ten balls and
independently recomputes an embedding centre. `--balls 0,4,9` selects more
centres. `--deep` additionally computes a noncentral time-one endpoint through
the actual nonlinear chain, rather than accepting a stored endpoint.

Fast regression tests check exact initial conditions and local tail queries for all ten balls,
gradients of the actual affine Hamiltonian against trajectory velocities,
a nonlinear inverse with a separately known solution, source validation,
an algebraic outside-image exclusion and serialized output accuracy:

```sh
uv run --python 3.12 --with python-flint==0.9.0 --with numpy==2.5.4 \
  python -m unittest discover -s examples -p 'test_*.py' -v
```

The fast suite also runs in CI. These are finite implementation checks, and
the mathematical argument uses the embedding and primitive contracts stated
above. There is no Python-to-Lean refinement proof or exhaustive machine
verification of all ambient inverse branches, and no uniform runtime bound.
The existing Lean theorems certify their own statements; they do not directly
certify this Python program.
