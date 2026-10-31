# Uniform executable packing

[`packing.py`](packing.py) is a single entry point for every integer `k >= 10`
and `0 < epsilon < 1`. It returns a finite, explicit global Hamiltonian and
supports rigorous value, gradient and actual-flow evaluation. The accompanying
Lean total algorithm proves termination and the packing property for all valid
inputs. There is no runtime or memory bound: ordinary high-density compilation
can take an astronomically long time.

## Run

From the repository root, install Elan and the toolchain in `lean-toolchain`,
then obtain the Mathlib dependency cache and build the executable proof target:

```sh
lake exe cache get
lake build verification.Executable
```

Python 3.12+ needs only `python-flint==0.9.0`. With `uv`, dependencies are read
from the entry point; alternatively install that package and use `python`:

```sh
uv run examples/packing.py --k 10 --epsilon 9999999999999999/10000000000000000
uv run examples/packing.py --k 12 --epsilon 9999999999999999/10000000000000000 \
  --query flow --time 1 --point 1/3 0 0 0 --output .lake/packing-example.json
```

These executable smoke examples deliberately use loose density requirements.
Their compiled zero Hamiltonian passes the **same full finite checker** as all
other outputs; independently, `R > 3*(k-1)+1` contains every original source ball.
They verify the execution path, not a high-density benchmark. A dense request is
valid and runs the general search, but is not a quick example:

```sh
uv run examples/packing.py --k 10 --epsilon 1/10
```

Progress goes to stderr; JSON goes to stdout. Build and search logs are saved
under `.lake/packing/`. There is no dependency on another worktree, archived
execution record or precomputed geometric table. Each call builds the current
proof target. As for the rest of the repository, a source rebuild or fresh kernel
replay provides stronger assurance than using previously compiled artifacts.

For repeated queries, compile once in Python:

```python
from fractions import Fraction
from examples.packing import compile_packing

H = compile_packing(10, Fraction(9999999999999999, 10**16))
print(H.radius)                       # exact rational target radius
print(H.value_gradient(1, [0, 0, 0, 0]))
print(H.trajectory(1, [Fraction(1, 3), 0, 0, 0]))
```

The default `backend='auto'` uses Arb for speed. `backend='rational'` (or CLI
`--backend rational`) selects the reference fallback using only Python integer
and rational arithmetic. It also activates automatically when a requested working
precision exceeds the Arb backend's machine-word limit or that backend overflows.
The fallback has no machine-word precision parameter. Both backends compute the
same exact function and flow; rational outputs have exact `lower`/`upper` endpoints
instead of decimal Arb intervals. Both require finite storage for any given run.

Coordinates are ambient `(q1,q2,p1,p2)`; source ball `i` is centred at
`(3*i,0,0,0)`, `0 <= i < k`. CLI numbers are exact rational strings. The library
also accepts a callable real name `x(p)` returning a rational with
`|x(p)-x| <= 2**(-p)`, for epsilon, time and each coordinate. Each oracle call must
terminate and all approximations must name the same real number. Noncomputable
reals require an oracle; finite input is not claimed to encode every real.
Inconsistent disjoint name intervals and fixed nonzero-width point balls are
rejected. Exact floats, if supplied through Python, denote their exact binary
rational value. A valid epsilon name in `(0,1)` eventually yields a positive
rational lower bound `e <= epsilon`; compiling for `e` preserves the original
strict density requirement.

## Mathematical contract and executable search

[`ExecutablePacking.lean`](../SymplecticPacking/Effective/ExecutablePacking.lean)
defines the **computable** functions `NativePacking.solveRational` and
`NativePacking.solveName`. Their return type `NativePacking.Output k epsilon`
contains a rational radius `R`, a finite candidate code `stage`, and a proof of

```text
Problem.EpochSpecR k epsilon R (PackingSearch.codeHamiltonian 2 (programCode stage)).
```

The specification in [`Problem.lean`](../verification/Problem.lean) requires
joint smoothness, a uniform compact spatial support, `R > 0`,
`k/R^4 > 1-epsilon`, existence of global integral curves from every source point,
and inclusion in the target closed ball at time one for **every** such integral
curve. Smoothness and compact support give uniqueness and a global symplectic
flow. The source and target are the original closed Euclidean balls.

The algorithm first finds a rational radius with
`k/(1-e/2) < R^4 < k/(1-e)`. Integer fourth-root trials are checked exactly;
the fallback enumerates rational codes, with termination proved by density.
It then enumerates finite rational-polynomial/Euler/grid certificates. Each
candidate has a decidable finite check, including every source and every grid
cell. Early rejection is proved equivalent to the original checker by
`checkStage_iff`. A zero-field seed is only an acceleration; after rejection,
`Nat.find` searches all natural candidate codes.

Completeness follows from the proved geometric construction, polynomial
approximation on a compact set, a strict target margin and sufficiently fine
grids/Euler meshes (`PackingSearch.exists_stage`). No runtime query asks whether
an arbitrary Hamiltonian has the packing property. Soundness uses a whole-cell
ODE error bound and proves the certified paths stay in the cutoff's plateau;
the checker’s internal clipped field therefore agrees with the actual output
field there (`PackingSearch.stage_sound`, `NativePacking.stage_epoch_spec`).
Geometric existence and termination proofs are erased during execution; only
finite rational arithmetic, finite checks and unbounded search remain.

The output is, for all real times,

```text
H(t,y) = product_j (1-S((y_j^2-(B/2)^2)/((3B/4)^2-(B/2)^2))) * P(t,y),
S(u) = expflat(u)/(expflat(u)+expflat(1-u)),
expflat(u) = exp(-1/u) for u>0, and 0 otherwise.
```

`B` is a positive integer and `P` a finite rational prefix-stack polynomial.
Time is not clipped in this output. The radius can differ from the geometric
paper's fixed formula; its exact strict density is part of the output contract.

## Rigorous interpretation and actual flow

The small [`_packing/`](_packing/) package implements those exact finite-code
semantics. Arb arithmetic encloses the polynomial and its full spatial
gradient; dual arithmetic gives the field `(H_p1,H_p2,-H_q1,-H_q2)`. At flat
seams, explicit real derivative bounds for `expflat` are used rather than
analytic continuation. The denominator has the global lower bound `exp(-2)`.
For any finite code, refining input names and arithmetic precision makes point
value and gradient enclosures converge, including at either seam.

`trajectory(T,x)` integrates this **same ambient field**, not an embedding
formula or a stored trajectory. It integrates
`dY/ds = T*X_H(T*s,Y)` on `s in [0,1]`, so negative, positive and zero real
times are covered. Each Arb step requires a Picard self-containing tube and a
real Taylor remainder valid on the entire tube; the rational backend uses the
direct integral enclosure described below. Returned enclosures must meet the
requested absolute radius. Serialization checks decimal Arb intervals or emits
the exact rational endpoints without rounding.

For any fixed finite `T` and `x`, compact spatial support bounds the field and
every required derivative on a compact time interval. Smoothness gives a finite
Lipschitz constant. At sufficiently small steps, Picard tubes strictly contain
their images and Taylor local remainders are uniformly `O(h^(r+1))`. Interval
propagation has amplification `1+O(h)` per step, hence a finite exponential
factor on this fixed interval. This statement also uses the **implemented interval
extension**: finite polynomial operations and division by a positive denominator
are locally width-Lipschitz; at flat seams the derivative-tail bounds are `o(r)`
as a seam-crossing interval of width `r` shrinks. Thus one step propagates width
as `(1+C*h)*rho + C*h^(r+1) + rounding`. Input and rounding radii can be made
small enough to meet any positive requested output error.

After an unsuccessful attempt the wrapper doubles precision, halves the maximum
step and quadruples its finite step budget. The Taylor order remains fixed and
at least two. Thus `h -> 0`, the available step budget eventually exceeds the
required `O(1/h)` steps, and input/rounding error decreases faster than that
budget grows. Each individual attempt is finite; there is no global retry,
precision or step cap. These facts establish convergence for every valid point
and time name. Precision is never increased while freezing rounded input data
as if it were exact. Unsuccessful attempts return no claimed enclosure.

The rational backend independently encloses `exp(-a)`: reduce `a` by powers of
two to `[0,1]`, use alternating Taylor sums with their next-term remainder, then
square intervals. For large `a`, `exp(-a) <= 2^(-a)` supplies a finite upper
bound. The flat derivative uses the endpoint values and unique maximum at `2`
of `t^2*exp(-t)`, with extra internal precision before multiplication by `t^2`.
Each operation rounds rational endpoints outward to a dyadic grid. Interval
width and rounding error therefore converge even at either flat seam.

Its flow evaluator uses strict Picard tubes and the integral enclosure
`Y(s+h) in Y(s)+h*F([s,s+h],tube)`. This is interval Euler with a local
`O(h^2)` width defect; it never assumes a sampled velocity is exact. Each attempt
has exactly `2^(a+4)` steps, each with at most 32 tube attempts. Failure restarts
with half the mesh size and double the arbitrary integer working precision.
The initial tube extends **every** coordinate by `2*h*(1+max(abs(F0)))` plus a
positive rounding guard. This gives an `O(h)` margin even when a coordinate has
zero initial velocity. Local width consistency then makes the first tube strict
for all sufficiently small steps; termination does not depend on 32 iterations
catching an arbitrarily small flat forcing. Already self-containing components
are preserved if further tube enlargement is attempted.
After certification, its Picard image also encloses the entire actual path;
the endpoint field is reevaluated on that smaller image to preserve invariant
coordinates without weakening the inclusion proof.
On a fixed compact query domain, sufficiently small steps have strict tubes and
width recurrence `(1+C*h)*rho+C*h^2+C*2^(-bits)`. Its global error tends to zero.
This independent finite-arithmetic path closes the Arb precision-parameter limit;
it trades speed for an unbounded reference implementation.

## Independent verification and trust boundary

```sh
lake build verification.Executable
lake env lean verification/Executable.lean
uv run --python 3.12 --with python-flint==0.9.0 \
  python -B -m unittest discover -s examples -p 'test_packing.py' -v
PACKING_NATIVE=1 uv run --python 3.12 --with python-flint==0.9.0 \
  python -B -m unittest discover -s examples -p 'test_packing.py' -v
bash scripts/verify.sh --lean
bash scripts/check_kernel.sh
```

The native tests exercise complete loose-density compilations, reject a dense
zero-field seed, compare a nonzero polynomial with exact Lean derivatives, and
compare nonzero actual flows with independent closed forms. Finite tests check
implementation paths; the all-parameter/all-point theorem is carried by the
Lean return type. Kernel replay now includes this executable algorithm.

The Lean kernel checks the total algorithm and full packing specification.
The constructive-dependency gates reject classical branching in runtime code;
axiom gates permit only `propext`, `Classical.choice`, `Quot.sound`. The gates
are metaprograms, not verified theorem provers. Standard execution also trusts
the Lean evaluator/compiler and the Python/FLINT runtime. The Python interpreter,
ODE evaluator and serialization have mathematical correspondence arguments and
execution tests, **not** a Lean-to-Python formal refinement proof.

This supplies an unrestricted executable algorithm and its mathematical
correctness proof. It does not establish compliance with Epoch's single-file,
PyTorch/autograd, 10-minute generation or 10-second evaluation requirements,
or official acceptance. Those are separate requirements in the
[official problem](https://epoch.ai/frontiermath/open-problems/symplectic-ball-packing).
The executable additions are subsequent to the archived v1.0.1 publication.
