#!/usr/bin/env python3
"""Deterministic builder (and --check verifier) for the unfinished experimental prototype
experiments/hamiltonian_lift/solution_hamiltonian.py from program/embedding_src/ and hamiltonian_src/.

STATUS: Experimental / Unfinished Research Prototype — NOT a passed or certified deliverable.

Usage:
    python3 experiments/hamiltonian_lift/build_hamiltonian.py          # regenerate solution_hamiltonian.py
    python3 experiments/hamiltonian_lift/build_hamiltonian.py --check  # verify byte-exact sync with modular sources
"""
from __future__ import annotations

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
EMB_DIR = HERE.parent.parent / "program" / "embedding_src"
HAM_DIR = HERE / "hamiltonian_src"
OUT_FILE = HERE / "solution_hamiltonian.py"

EMB_ORDER = ("primitives", "keyhole", "comparator", "twists", "transfer", "chain")
FLOW_SOURCES = (
    ("h_primitives", HAM_DIR / "h_primitives.py"),
    ("chain_primitive", HAM_DIR / "chain_primitive.py"),
    ("hamiltonian_general", HAM_DIR / "hamiltonian_general.py"),
)
ORDER = EMB_ORDER + tuple(name for name, _ in FLOW_SOURCES)

HEADER = '''"""EXPERIMENTAL / UNFINISHED RESEARCH PROTOTYPE: multi-stage Hamiltonian-lift exploration (`solution_hamiltonian.py`).

STATUS: Experimental / Unfinished — NOT a passed or certified deliverable (do NOT cite as a verified global C^3
Hamiltonian implementation; see experiments/hamiltonian_lift/README.md and DIAGNOSTICS.md).

Generated deterministically from program/embedding_src/ and experiments/hamiltonian_lift/hamiltonian_src/ by
experiments/hamiltonian_lift/build_hamiltonian.py. Explores lifting Paper IV's closed-form C^4 symplectic packing
chain (`Chain3`, paper/p4/main.pdf, Section 8) into Epoch AI's `Hamiltonian(Q, P, t)` PyTorch float64 interface.

Interface:
    solution(k, eps) returns self-contained Python source defining
        Hamiltonian(Q, P, t) -> H            Epoch AI interface: Q, P of shape (N, 2) in torch.float64, scalar float t
                                             (also accepts per-row 1D tensor t of shape (N,) for multi-rate solvers);
                                             returns H of shape (N,) in torch.float64. Spatial vector field
                                             (dQ/dt, dP/dt) = (+dH/dP, -dH/dQ) is computed via torch.autograd.grad.
        CONFIG                               parameters, analytic margins of (H0)-(H15), stage breaks, and support radius.
        Embed(i, X) / Preimage(j, Y)         underlying Paper IV time-1 closed-form symplectic maps (with experimental
                                             parameter overrides when selected by GeneralPackingHamiltonian).
        ExactTrajectory(t, X_local, i)       candidate isotopy curve gamma_t^{(i)}(X_local) on |X_local| <= 1.
        ExactTrajectoryAndVelocity(t, X, i)  candidate (gamma_t^{(i)}(X), d/dt gamma_t^{(i)}(X)) diagnostic
                                             (six-point Gauss-Legendre integral evaluation for 0 < rho <= 1e-4).
    Coordinates (q1, q2, p1, p2) with Q = (q1, q2), P = (p1, p2), omega_0 = dq1 ^ dp1 + dq2 ^ dp2;
    initial unit balls are centred at (3*i, 0, 0, 0) for i = 0..k-1, and target radius is R = (k / (1 - eps))^(1/4).

Scope and known limitations (see README.md & DIAGNOSTICS.md):
  * Paper IV, Proposition 8.1 proves the radial-collar Liouville generator formula in terms of the global radial
    Poincare primitive and abstract ODE trajectory certificates (also formalised abstractly in Lean 4 in
    verification/RK4Convergence.lean); neither Paper IV nor Lean 4 certifies this 6-stage prototype or its modified
    implementation parameters, sampled collar radii, autograd patches, or finite ray-bisection sheet unwrapping.
  * In Stages 0-4, collar radii, tau, and 4D translation lift amplitudes are selected by finite directional/time
    sampling heuristics rather than analytic all-(k, eps) disjointness bounds; only Stage 5's open-ball image
    disjointness follows from dividing f_i(B^0(r_dom)) by v > 0.
  * In Stages 9-11 (`Transfer3`), straight radial ray unwrapping exhibits unresolved integer-turn scalar jumps across
    cutoff collars near small |Z_0| (e.g. k = 12, eps = 0.001, ball 11 in repro_branch_jump.py and
    logs/current_honest_check.log), in addition to the local seam-constant discrepancy recorded in DIAGNOSTICS.md.
"""
'''

RUNTIME_BLOCK = '''
_RUNTIME = r"""
import sys as _sys, types as _types
import torch
torch.set_default_dtype(torch.float64)
_saved_mods = {_n: _sys.modules.get(_n) for _n in _ORDER}
try:
    for _name in _ORDER:
        _m = _types.ModuleType(_name)
        _m.__file__ = '/nonexistent/embedded/' + _name + '.py'
        _sys.modules[_name] = _m
        exec(compile(_SRC[_name], '<embedded ' + _name + '>', 'exec'), _m.__dict__)
    _hg_mod = _sys.modules['hamiltonian_general']
    _H_OBJ = _hg_mod.GeneralPackingHamiltonian(_K, _EPS)
finally:
    for _name, _prev in _saved_mods.items():
        if _prev is None:
            _sys.modules.pop(_name, None)
        else:
            _sys.modules[_name] = _prev

_CH = _H_OBJ.cp.ch
CONFIG = dict(
    _CH.config,
    k=_K,
    eps=_EPS,
    R_needed=_H_OBJ.R_needed,
    R_cell=_CH.R,
    R_image_bound=_CH.Rs,
    r_domain=_H_OBJ.r_dom,
    tau=_H_OBJ.tau,
    support_radius=_H_OBJ.support_radius,
    t_breaks=list(_H_OBJ.T_BREAKS),
    hypotheses={n: m for n, (ok, m) in _CH.hyp.items()},
    theorem='Theorem 1.1 of ' + _CH.config['proof'],
)


def Hamiltonian(Q, P, t):
    if not torch.is_tensor(t):
        t = float(t)
    return _H_OBJ(Q.to(torch.float64), P.to(torch.float64), t)


def Embed(i, X):
    return _CH.Embed(int(i), X.to(torch.float64))


def Preimage(j, Y):
    return _CH.Preimage(int(j), Y.to(torch.float64))


def ExactTrajectory(t, X_local, i):
    return _H_OBJ.exact_trajectory(float(t), X_local.to(torch.float64), int(i))


def ExactTrajectoryAndVelocity(t, X_local, i):
    return _H_OBJ.exact_trajectory_and_velocity(float(t), X_local.to(torch.float64), int(i))
"""

_probe = {}


def _load():
    if "chain" not in _probe:
        import sys, types
        saved = {name: sys.modules.get(name) for name in _ORDER}
        try:
            for name in _ORDER[:6]:
                m = types.ModuleType(name)
                m.__file__ = "/nonexistent/embedded/" + name + ".py"
                sys.modules[name] = m
                exec(compile(_SRC[name], "<embedded " + name + ">", "exec"), m.__dict__)
            _probe["chain"] = sys.modules["chain"]
        finally:
            for name, prev in saved.items():
                if prev is None:
                    sys.modules.pop(name, None)
                else:
                    sys.modules[name] = prev
    return _probe["chain"]


def solution(k, epsilon):
    if isinstance(k, bool) or int(k) != k or k < 10 or not (0.0 < float(epsilon) < 1.0):
        raise ValueError("need an integer k >= 10 and 0 < epsilon < 1")
    k = int(k)
    epsilon = float(epsilon)
    _load().Chain3(k, epsilon)  # raises ValueError if any float64 hypothesis margin (H0)-(H15) fails
    return ("_K = %d\\n_EPS = %r\\n_ORDER = %r\\n_SRC = %r\\n" % (k, epsilon, _ORDER, _SRC)) + _RUNTIME
'''


def render() -> str:
    parts = [HEADER, f"_ORDER = {list(ORDER)!r}\n\n_SRC = {{\n"]
    sources: list[tuple[str, Path]] = [(name, EMB_DIR / f"{name}.py") for name in EMB_ORDER] + list(FLOW_SOURCES)
    for name, path in sources:
        text = path.read_text(encoding="utf-8")
        if "'''" in text:
            raise ValueError(f"{path} must not contain triple single-quotes")
        if text.endswith("\\"):
            raise ValueError(f"{path} must not end with a backslash")
        parts.append(f"    {name!r}: r'''{text}''',\n")
    parts.append("}\n")
    parts.append(RUNTIME_BLOCK)
    return "".join(parts)


def main() -> None:
    expected = render()
    if "--check" in sys.argv[1:]:
        actual = OUT_FILE.read_text(encoding="utf-8") if OUT_FILE.exists() else ""
        if actual != expected:
            print("ERROR: experiments/hamiltonian_lift/solution_hamiltonian.py is out of sync with modular sources", file=sys.stderr)
            sys.exit(1)
        print("Hamiltonian bundle check: PASS")
        return
    OUT_FILE.write_text(expected, encoding="utf-8")
    print(f"Wrote {OUT_FILE} ({len(expected.splitlines())} lines, {len(expected)} bytes)")


if __name__ == "__main__":
    main()
