#!/usr/bin/env python3
"""Deterministic builder (and --check verifier) for standalone program/solution_embedding.py
from the modular sources in program/embedding_src/.

Usage:
    python3 program/build_embedding.py          # regenerate program/solution_embedding.py
    python3 program/build_embedding.py --check  # verify byte-exact sync with program/embedding_src/
"""
from __future__ import annotations

import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
SRC_DIR = HERE / "embedding_src"
OUT_FILE = HERE / "solution_embedding.py"

ORDER = ("primitives", "keyhole", "comparator", "twists", "transfer", "chain")

HEADER = '''"""Explicit closed-form C^4 symplectic packings of the four-ball by k unit balls.

Generated deterministically from the modular sources in program/embedding_src/ by program/build_embedding.py.
Complete mathematical proofs of all stages and parameter bounds are given in Paper IV (paper/p4/main.pdf).

Interface (a direct-map counterpart of the Epoch AI format: embeddings instead of an ODE Hamiltonian):
    solution(k, eps) returns self-contained Python source defining
        Embed(i, X) -> Y           the i-th embedding f_i, i = 0..k-1; X of shape (n, 4) in coordinates centred at
                                   ball i, |X| <= 1; Y of shape (n, 4) in the target R^4.
        Preimage(j, Y) -> (X, ok)  left inverse of f_j on B^o(R_s); ok = False means Y has no preimage in B^o(r_+).
        STAGES(i)                  the conformally symplectic stage factors of f_i with their inverses.
        CONFIG                     parameters, analytic margins of (H0)-(H15), and float64 self-test diagnostics.
    Coordinates (q1, q2, p1, p2), omega_0 = dq1 ^ dp1 + dq2 ^ dp2, R = (k / (1 - eps))^(1/4).

Mathematical scope vs. float64 scope:
  * Over exact real numbers (with exact scalar roots in KR^-1 and KS_tau), Theorem 1.1 of Paper IV proves that for
    every integer k >= 10 and every real eps in (0, 1), there is r_+ = sqrt(a / rho_b) > 1 such that f_0, ..., f_{k-1}
    are C^4 symplectic embeddings of B^o(r_+) into B^o(R) with pairwise disjoint images, and Preimage(i, .) is an
    exact left inverse on f_i(B^o(r_+)).
  * In IEEE-754 float64, solution(k, eps) evaluates the analytic margins of (H0)-(H15) on the float64 parameters and
    raises ValueError if rounding underflows any strict margin (e.g. eps <= 1e-16 where 1.0 - eps == 1.0). Because
    the maps have steep local Lipschitz constants (~ 10^8 - 10^15 as eps -> 0 or k grows), float64 evaluation loses
    precision for extreme (k, eps); see program/README.md and program/check_embedding_mp.py.
"""
'''

RUNTIME_BLOCK = '''
_RUNTIME = r"""
import sys as _sys, types as _types
import torch
torch.set_default_dtype(torch.float64)
for _name in _ORDER:
    _m = _types.ModuleType(_name)
    _m.__file__ = '/nonexistent/embedded/' + _name + '.py'
    _sys.modules[_name] = _m
    exec(compile(_SRC[_name], '<embedded ' + _name + '>', 'exec'), _m.__dict__)
_ch_mod = _sys.modules['chain']
_CH = _ch_mod.Chain3(_K, _EPS)
CONFIG = dict(
    _CH.config,
    k=_K,
    eps=_EPS,
    R_needed=_CH.R_requested,
    R_cell=_CH.R,
    R_image_bound=_CH.Rs,
    hypotheses={n: m for n, (ok, m) in _CH.hyp.items()},
    theorem='Theorem 1.1 of ' + _ch_mod.PROOF,
)
CONFIG['float64_selftest'] = _ch_mod.selftest(_CH)
_cache = {}


def Embed(i, X):
    return _CH.Embed(int(i), X.to(torch.float64))


def Preimage(j, Y):
    Y = Y.to(torch.float64)
    hit = _cache.get('Y')
    if hit is None or hit.shape != Y.shape or not torch.equal(hit, Y):
        _cache['Y'] = Y.detach().clone()
        _cache['flat'] = _CH.target_to_flat(Y)[0]
    return _CH.Preimage(int(j), Y, flat=_cache['flat'])


def STAGES(i):
    return _ch_mod.stage_dicts(_CH, int(i))
"""

_probe = {}


def _load():
    if "chain" not in _probe:
        import sys, types
        saved = {name: sys.modules.get(name) for name in _ORDER}
        try:
            for name in _ORDER:
                m = types.ModuleType(name)
                m.__file__ = "/nonexistent/embedded/" + name + ".py"
                sys.modules[name] = m
                exec(compile(_SRC[name], "<embedded " + name + ">", "exec"), m.__dict__)
            _probe["chain"] = sys.modules["chain"]
            _probe["mods"] = {name: sys.modules[name] for name in _ORDER}
        finally:
            for name, prev in saved.items():
                if prev is None:
                    sys.modules.pop(name, None)
                else:
                    sys.modules[name] = prev
    return _probe["chain"]


def solution(k, eps):
    if int(k) != k or k < 10 or not (0.0 < float(eps) < 1.0):
        raise ValueError("need an integer k >= 10 and 0 < eps < 1")
    k = int(k)
    eps = float(eps)
    _load().Chain3(k, eps)  # raises ValueError if any float64 hypothesis margin fails
    return ("_K = %d\\n_EPS = %r\\n_ORDER = %r\\n_SRC = %r\\n" % (k, eps, _ORDER, _SRC)) + _RUNTIME
'''


def render() -> str:
    parts = [HEADER, f"_ORDER = {list(ORDER)!r}\n\n_SRC = {{\n"]
    for name in ORDER:
        p = SRC_DIR / f"{name}.py"
        text = p.read_text(encoding="utf-8")
        if "'''" in text:
            raise ValueError(f"{p} must not contain triple single-quotes")
        if text.endswith("\\"):
            raise ValueError(f"{p} must not end with a backslash")
        parts.append(f"    {name!r}: r'''{text}''',\n")
    parts.append("}\n")
    parts.append(RUNTIME_BLOCK)
    return "".join(parts)


def main() -> None:
    expected = render()
    if "--check" in sys.argv[1:]:
        actual = OUT_FILE.read_text(encoding="utf-8") if OUT_FILE.exists() else ""
        if actual != expected:
            print("ERROR: program/solution_embedding.py is out of sync with program/embedding_src/", file=sys.stderr)
            sys.exit(1)
        print("Embedding bundle check: PASS")
        return
    OUT_FILE.write_text(expected, encoding="utf-8")
    print(f"Wrote {OUT_FILE} ({len(expected.splitlines())} lines, {len(expected)} bytes)")


if __name__ == "__main__":
    main()
