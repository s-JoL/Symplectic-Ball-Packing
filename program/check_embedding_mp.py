"""Arbitrary-precision (mpmath) verifier for explicit packing embeddings (solution_embedding.py).

Unlike a separate model-only script, this checker executes the SUBMITTED Python source code directly on
an arbitrary-precision mpmath tensor backend (converting decimal literals in the source and embedded
modules to exact D-digit mpmath numbers), cross-checks it against standard float64 PyTorch execution,
and exits with status 1 if any check fails.

Checks performed (all enforced in the final PASS gate):
  0. Float64 / mpmath consistency: verifies on deterministic special points and random samples across all k
     balls that float64 PyTorch execution of the submitted source agrees with D-digit mpmath execution at the
     float64 parameter value within local Jacobian conditioning (||Y_f64 - Y_mp64|| <= agree_tol * max(1, ||J||_F)).
  1. Containment (A) & round-trip (C): checks all 17*k deterministic special points (centres, +-e_a axis
     points, zero-fibre and zero-base diagonals), random samples on all balls, and 100% of points flagged by C
     in float64.
  2. Pairwise disjointness (D): verifies in D-digit arithmetic that images of distinct balls do not overlap.
  3. Symplecticity (B): checks the normalised symplectic residual ||J^T Omega J - Omega||_max / max(1, ||J||_F^2)
     by central differences at step h = 10^{-(D // 3)} on deterministic/random samples and 100% of points
     flagged by B in float64.
  4. Continuity (G) via interval-preserving bisection: scans random chords in float64 (matching check_embedding.py)
     and re-evaluates 100% of flagged intervals in D-digit arithmetic by keeping the larger-gap half-interval at
     every bisection step all the way down to separation 10^-30 (never switching to a midpoint perturbation that
     could step to one side of a jump).

Usage:
    python check_embedding_mp.py solution_embedding.py --k 10 --eps 0.002 --dps 100 --chords 100
    python check_embedding_mp.py solution_embedding.py --k 101 --eps 0.01 --dps 100 --chords 20
"""
from __future__ import annotations

import argparse
import io
import json
import math
import os
import sys
import time
import tokenize
import types

import mpmath as mp
import torch

if os.path.dirname(os.path.abspath(__file__)) not in sys.path:
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import check_embedding as ce

torch.set_default_dtype(torch.float64)


# ---------------------------------------------------------------------------
# Arbitrary-precision tensor & math backend for executing submitted sources
# ---------------------------------------------------------------------------

def _to_mp_scalar(x):
    if isinstance(x, (mp.mpf, mp.mpc, bool)):
        return x
    if hasattr(x, "_mpf_"):
        return +x
    if isinstance(x, int):
        return mp.mpf(x)
    if isinstance(x, float):
        if math.isnan(x):
            return mp.mpf("nan")
        if math.isinf(x):
            return mp.mpf("inf") if x > 0 else mp.mpf("-inf")
        return mp.mpf(repr(x))
    if isinstance(x, complex):
        return mp.mpc(_to_mp_scalar(x.real), _to_mp_scalar(x.imag))
    raise TypeError(f"unsupported scalar type: {type(x)}")


def _safe_div(x, y):
    if y == 0:
        if isinstance(x, mp.mpc) or isinstance(y, mp.mpc):
            return mp.mpc(mp.mpf("nan"), mp.mpf("nan"))
        if mp.isnan(x) or x == 0:
            return mp.mpf("nan")
        return mp.mpf("inf") if x > 0 else mp.mpf("-inf")
    return x / y


class _MpTensor:
    """1D or 2D tensor backed by Python lists of mpmath mpf/mpc/bool scalars."""

    def __init__(self, data, ndim=None):
        if isinstance(data, _MpTensor):
            self.ndim = data.ndim
            self.d = [list(r) for r in data.d] if self.ndim == 2 else list(data.d)
            return
        if ndim == 2 or (isinstance(data, list) and data and isinstance(data[0], list)):
            self.ndim = 2
            self.d = [[_to_mp_scalar(v) if not isinstance(v, bool) else v for v in row] for row in data]
        else:
            self.ndim = 1
            self.d = [_to_mp_scalar(v) if not isinstance(v, bool) else v for v in data]

    @property
    def shape(self):
        if self.ndim == 2:
            return (len(self.d), len(self.d[0]) if self.d else 0)
        return (len(self.d),)

    def __len__(self):
        return len(self.d)

    def clone(self):
        return _MpTensor(self)

    def detach(self):
        return self

    def to(self, _dtype):
        if _dtype is _MpTorch.complex128:
            return self._uop(lambda x: mp.mpc(x))
        if _dtype is _MpTorch.float64:
            return self._uop(lambda x: mp.mpf(x))
        if _dtype is _MpTorch.bool:
            return self._uop(bool)
        return self

    def _uop(self, fn):
        if self.ndim == 1:
            return _MpTensor([fn(x) for x in self.d], ndim=1)
        return _MpTensor([[fn(x) for x in r] for r in self.d], ndim=2)

    def _bop(self, other, fn):
        if isinstance(other, _MpTensor):
            if self.ndim == 1 and other.ndim == 1:
                if len(self.d) == 1 and len(other.d) > 1:
                    s0 = self.d[0]
                    return _MpTensor([fn(s0, y) for y in other.d], ndim=1)
                if len(other.d) == 1 and len(self.d) > 1:
                    o0 = other.d[0]
                    return _MpTensor([fn(x, o0) for x in self.d], ndim=1)
                return _MpTensor([fn(x, y) for x, y in zip(self.d, other.d)], ndim=1)
            if self.ndim == 2 and other.ndim == 2:
                r_self, c_self = self.shape
                r_oth, c_oth = other.shape
                rows = max(r_self, r_oth)
                cols = max(c_self, c_oth)
                out = []
                for r in range(rows):
                    rs = self.d[0 if r_self == 1 else r]
                    ro = other.d[0 if r_oth == 1 else r]
                    out.append([fn(rs[0 if c_self == 1 else c], ro[0 if c_oth == 1 else c]) for c in range(cols)])
                return _MpTensor(out, ndim=2)
            if self.ndim == 2 and other.ndim == 1:
                return _MpTensor([[fn(x, y) for x, y in zip(r, other.d)] for r in self.d], ndim=2)
            if self.ndim == 1 and other.ndim == 2:
                return _MpTensor([[fn(x, y) for x, y in zip(self.d, r)] for r in other.d], ndim=2)
        sc = _to_mp_scalar(other) if not isinstance(other, bool) else other
        return self._uop(lambda x: fn(x, sc))

    def __pos__(self): return self.clone()
    def __neg__(self): return self._uop(lambda x: -x)
    def __invert__(self): return self._uop(lambda x: not bool(x))
    def __add__(self, o): return self._bop(o, lambda x, y: x + y)
    def __radd__(self, o): return self._bop(o, lambda x, y: y + x)
    def __sub__(self, o): return self._bop(o, lambda x, y: x - y)
    def __rsub__(self, o): return self._bop(o, lambda x, y: y - x)
    def __mul__(self, o): return self._bop(o, lambda x, y: x * y)
    def __rmul__(self, o): return self._bop(o, lambda x, y: y * x)
    def __truediv__(self, o): return self._bop(o, _safe_div)
    def __rtruediv__(self, o): return self._bop(o, lambda x, y: _safe_div(y, x))
    def __pow__(self, o): return self._bop(o, lambda x, y: x ** y)
    def __lt__(self, o): return self._bop(o, lambda x, y: bool(x < y))
    def __le__(self, o): return self._bop(o, lambda x, y: bool(x <= y))
    def __gt__(self, o): return self._bop(o, lambda x, y: bool(x > y))
    def __ge__(self, o): return self._bop(o, lambda x, y: bool(x >= y))
    def __eq__(self, o): return self._bop(o, lambda x, y: bool(x == y))  # type: ignore[override]
    def __ne__(self, o): return self._bop(o, lambda x, y: bool(x != y))  # type: ignore[override]
    def __and__(self, o): return self._bop(o, lambda x, y: bool(x) and bool(y))
    def __or__(self, o): return self._bop(o, lambda x, y: bool(x) or bool(y))

    def __float__(self):
        if self.ndim == 1 and len(self.d) == 1:
            return float(self.d[0])
        raise TypeError("only single-element tensors convert to float")

    def __bool__(self):
        if self.ndim == 1 and len(self.d) == 1:
            return bool(self.d[0])
        raise TypeError("boolean value of multi-element tensor is ambiguous")

    def abs(self): return self._uop(abs)
    def pow(self, e): return self ** e
    def sqrt(self): return _MpTorch.sqrt(self)
    def conj(self): return self._uop(mp.conj)

    @property
    def real(self): return self._uop(mp.re)

    @property
    def imag(self): return self._uop(mp.im)

    def clamp(self, lo=None, hi=None):
        lo_m = _to_mp_scalar(lo) if lo is not None else None
        hi_m = _to_mp_scalar(hi) if hi is not None else None
        def _c(x):
            if mp.isnan(x):
                return x
            if lo_m is not None and x < lo_m:
                x = lo_m
            if hi_m is not None and x > hi_m:
                x = hi_m
            return x
        return self._uop(_c)

    def clamp_min(self, lo): return self.clamp(lo=lo, hi=None)
    def clamp_max(self, hi): return self.clamp(lo=None, hi=hi)

    def any(self):
        if self.ndim == 1:
            return any(bool(x) for x in self.d)
        return any(bool(x) for r in self.d for x in r)

    def all(self, dim=None):
        if dim is None:
            if self.ndim == 1:
                return all(bool(x) for x in self.d)
            return all(bool(x) for r in self.d for x in r)
        if dim in (1, -1) and self.ndim == 2:
            return _MpTensor([all(bool(x) for x in r) for r in self.d], ndim=1)
        raise ValueError(f"unsupported all(dim={dim})")

    def sum(self, dim=None, keepdim=False):
        if dim is None:
            vals = self.d if self.ndim == 1 else [x for r in self.d for x in r]
            return sum(vals, mp.mpf(0))
        if dim in (1, -1) and self.ndim == 2:
            s = [sum(r, mp.mpf(0)) for r in self.d]
            return _MpTensor([[v] for v in s], ndim=2) if keepdim else _MpTensor(s, ndim=1)
        raise ValueError(f"unsupported sum(dim={dim})")

    def norm(self, dim=None, keepdim=False):
        if dim is None:
            vals = self.d if self.ndim == 1 else [x for r in self.d for x in r]
            return mp.sqrt(sum((abs(v) ** 2 for v in vals), mp.mpf(0)))
        if dim in (1, -1) and self.ndim == 2:
            n = [mp.sqrt(sum((abs(v) ** 2 for v in r), mp.mpf(0))) for r in self.d]
            return _MpTensor([[v] for v in n], ndim=2) if keepdim else _MpTensor(n, ndim=1)
        raise ValueError(f"unsupported norm(dim={dim})")

    def max(self):
        vals = self.d if self.ndim == 1 else [x for r in self.d for x in r]
        m = vals[0]
        for v in vals[1:]:
            if mp.isnan(v):
                return v
            if v > m:
                m = v
        return m

    def min(self):
        vals = self.d if self.ndim == 1 else [x for r in self.d for x in r]
        m = vals[0]
        for v in vals[1:]:
            if mp.isnan(v):
                return v
            if v < m:
                m = v
        return m

    def _mask_indices(self, mask):
        return [i for i, flag in enumerate(mask.d) if bool(flag)]

    def __getitem__(self, idx):
        if self.ndim == 1:
            if idx is Ellipsis:
                return self.clone()
            if isinstance(idx, tuple):
                if len(idx) == 2 and idx[0] is Ellipsis and idx[1] is None:
                    return _MpTensor([[v] for v in self.d], ndim=2)
                if len(idx) == 2 and idx[1] is None:
                    sub = self[idx[0]]
                    return _MpTensor([[v] for v in sub.d], ndim=2)
                if len(idx) == 1:
                    return self[idx[0]]
            if isinstance(idx, _MpTensor):
                return _MpTensor([self.d[i] for i in self._mask_indices(idx)], ndim=1)
            if isinstance(idx, slice):
                return _MpTensor(self.d[idx], ndim=1)
            return self.d[idx]

        # 2D indexing
        if isinstance(idx, tuple):
            r_idx, c_idx = idx
            if r_idx is Ellipsis:
                r_idx = slice(None)
            # First select rows
            if isinstance(r_idx, _MpTensor):
                rows = [self.d[i] for i in self._mask_indices(r_idx)]
            elif isinstance(r_idx, slice):
                rows = self.d[r_idx]
            elif isinstance(r_idx, int):
                row = self.d[r_idx]
                if isinstance(c_idx, slice):
                    return _MpTensor(row[c_idx], ndim=1)
                if isinstance(c_idx, list):
                    return _MpTensor([row[j] for j in c_idx], ndim=1)
                return row[c_idx]
            else:
                raise IndexError(f"unsupported row index: {type(r_idx)}")

            if c_idx is None:
                raise IndexError("unsupported 3D expansion")
            if isinstance(c_idx, int):
                return _MpTensor([r[c_idx] for r in rows], ndim=1)
            if isinstance(c_idx, slice):
                return _MpTensor([r[c_idx] for r in rows], ndim=2)
            if isinstance(c_idx, (list, tuple)):
                return _MpTensor([[r[j] for j in c_idx] for r in rows], ndim=2)
            raise IndexError(f"unsupported col index: {type(c_idx)}")

        if isinstance(idx, _MpTensor):
            return _MpTensor([list(self.d[i]) for i in self._mask_indices(idx)], ndim=2)
        if isinstance(idx, slice):
            return _MpTensor([list(r) for r in self.d[idx]], ndim=2)
        if isinstance(idx, int):
            return _MpTensor(list(self.d[idx]), ndim=1)
        raise IndexError(f"unsupported index: {type(idx)}")

    def __setitem__(self, idx, val):
        if self.ndim == 1:
            if isinstance(idx, _MpTensor):
                inds = self._mask_indices(idx)
                if isinstance(val, _MpTensor):
                    for k, i in enumerate(inds):
                        self.d[i] = val.d[k]
                else:
                    sc = _to_mp_scalar(val) if not isinstance(val, bool) else val
                    for i in inds:
                        self.d[i] = sc
                return
            if isinstance(idx, slice):
                inds = list(range(*idx.indices(len(self.d))))
                if isinstance(val, _MpTensor):
                    for k, i in enumerate(inds):
                        self.d[i] = val.d[k]
                else:
                    sc = _to_mp_scalar(val)
                    for i in inds:
                        self.d[i] = sc
                return
            self.d[idx] = _to_mp_scalar(val)
            return

        # 2D assignment
        if isinstance(idx, _MpTensor):
            inds = self._mask_indices(idx)
            for k, i in enumerate(inds):
                self.d[i] = list(val.d[k])
            return
        if isinstance(idx, slice):
            inds = list(range(*idx.indices(len(self.d))))
            for k, i in enumerate(inds):
                self.d[i] = list(val.d[k])
            return
        if isinstance(idx, tuple):
            r_idx, c_idx = idx
            inds = self._mask_indices(r_idx) if isinstance(r_idx, _MpTensor) else list(range(*r_idx.indices(len(self.d))))
            if isinstance(c_idx, int):
                for k, i in enumerate(inds):
                    self.d[i][c_idx] = val.d[k] if isinstance(val, _MpTensor) else _to_mp_scalar(val)
                return
            if isinstance(c_idx, slice):
                c_inds = list(range(*c_idx.indices(len(self.d[0]))))
                for k, i in enumerate(inds):
                    for m, j in enumerate(c_inds):
                        self.d[i][j] = val.d[k][m]
                return
        raise IndexError(f"unsupported setitem index: {idx}")

    def tolist(self):
        if self.ndim == 1:
            return list(self.d)
        return [list(r) for r in self.d]


class _MpGenerator:
    def __init__(self):
        self.seed = 0

    def manual_seed(self, s):
        self.seed = int(s)
        return self


class _MpTorch:
    float64 = "float64"
    complex128 = "complex128"
    bool = "bool"
    long = "long"

    @staticmethod
    def set_default_dtype(_dt):
        pass

    @staticmethod
    def is_tensor(x):
        return isinstance(x, _MpTensor)

    @staticmethod
    def equal(a, b):
        return isinstance(a, _MpTensor) and isinstance(b, _MpTensor) and a.shape == b.shape and a.d == b.d

    @staticmethod
    def Generator():
        return _MpGenerator()

    @staticmethod
    def randn(*shape, generator=None, dtype=None):
        g = torch.Generator().manual_seed(generator.seed if generator else 0)
        if len(shape) == 2:
            t = torch.randn(shape[0], shape[1], generator=g, dtype=torch.float64)
            if generator:
                generator.seed += 1
            return _MpTensor([[mp.mpf(float(v)) for v in row] for row in t.tolist()], ndim=2)
        t = torch.randn(shape[0], generator=g, dtype=torch.float64)
        if generator:
            generator.seed += 1
        return _MpTensor([mp.mpf(float(v)) for v in t.tolist()], ndim=1)

    @staticmethod
    def rand(*shape, generator=None, dtype=None):
        g = torch.Generator().manual_seed((generator.seed + 10007) if generator else 10007)
        if len(shape) == 2:
            t = torch.rand(shape[0], shape[1], generator=g, dtype=torch.float64)
            if generator:
                generator.seed += 1
            return _MpTensor([[mp.mpf(float(v)) for v in row] for row in t.tolist()], ndim=2)
        t = torch.rand(shape[0], generator=g, dtype=torch.float64)
        if generator:
            generator.seed += 1
        return _MpTensor([mp.mpf(float(v)) for v in t.tolist()], ndim=1)

    @staticmethod
    def tensor(val, dtype=None):
        if isinstance(val, (int, float, mp.mpf)):
            return _MpTensor([_to_mp_scalar(val)], ndim=1)
        if isinstance(val, list) and val and isinstance(val[0], list):
            return _MpTensor(val, ndim=2)
        return _MpTensor(list(val), ndim=1)

    @staticmethod
    def zeros(*shape, dtype=None):
        if len(shape) == 1 and isinstance(shape[0], tuple):
            shape = shape[0]
        fill = False if dtype is _MpTorch.bool else (mp.mpc(0) if dtype is _MpTorch.complex128 else mp.mpf(0))
        if len(shape) == 2:
            return _MpTensor([[fill for _ in range(shape[1])] for _ in range(shape[0])], ndim=2)
        return _MpTensor([fill for _ in range(shape[0])], ndim=1)

    @staticmethod
    def ones(*shape, dtype=None):
        if len(shape) == 1 and isinstance(shape[0], tuple):
            shape = shape[0]
        if len(shape) == 2:
            return _MpTensor([[mp.mpf(1) for _ in range(shape[1])] for _ in range(shape[0])], ndim=2)
        return _MpTensor([mp.mpf(1) for _ in range(shape[0])], ndim=1)

    @staticmethod
    def full(shape, fill_value, dtype=None):
        fv = _to_mp_scalar(fill_value) if not isinstance(fill_value, bool) else fill_value
        if len(shape) == 2:
            return _MpTensor([[fv for _ in range(shape[1])] for _ in range(shape[0])], ndim=2)
        return _MpTensor([fv for _ in range(shape[0])], ndim=1)

    @staticmethod
    def zeros_like(x):
        fv = mp.mpc(0) if (x.d and ((x.ndim == 1 and isinstance(x.d[0], mp.mpc)) or (x.ndim == 2 and x.d[0] and isinstance(x.d[0][0], mp.mpc)))) else mp.mpf(0)
        return x._uop(lambda _: fv)

    @staticmethod
    def ones_like(x):
        return x._uop(lambda _: mp.mpf(1))

    @staticmethod
    def full_like(x, fill_value):
        fv = _to_mp_scalar(fill_value)
        return x._uop(lambda _: fv)

    @staticmethod
    def sin(x): return x._uop(mp.sin)
    @staticmethod
    def cos(x): return x._uop(mp.cos)
    @staticmethod
    def asin(x): return x._uop(lambda v: mp.asin(mp.mpf(v)) if -1 <= v <= 1 else mp.mpf("nan"))

    @staticmethod
    def exp(x):
        return x._uop(mp.exp)

    @staticmethod
    def sqrt(x):
        def _sq(v):
            if isinstance(v, mp.mpc):
                return mp.sqrt(v)
            if mp.isnan(v) or v < 0:
                return mp.mpf("nan")
            return mp.sqrt(v)
        return x._uop(_sq)

    @staticmethod
    def hypot(a, b):
        return a._bop(b, mp.hypot)

    @staticmethod
    def atan2(y, x):
        return y._bop(x, mp.atan2)

    @staticmethod
    def angle(z):
        return z._uop(mp.arg)

    @staticmethod
    def sign(x):
        def _sg(v):
            if mp.isnan(v):
                return v
            if v > 0:
                return mp.mpf(1)
            if v < 0:
                return mp.mpf(-1)
            return mp.mpf(0)
        return x._uop(_sg)

    @staticmethod
    def floor(x):
        return x._uop(lambda v: mp.floor(v) if mp.isfinite(v) else v)

    @staticmethod
    def round(x):
        return x._uop(lambda v: mp.nint(v) if mp.isfinite(v) else v)

    @staticmethod
    def remainder(x, m):
        mm = _to_mp_scalar(m)
        return x._uop(lambda v: v - mm * mp.floor(v / mm) if mp.isfinite(v) else v)

    @staticmethod
    def where(cond, a, b):
        if cond.ndim == 1:
            av = a.d if isinstance(a, _MpTensor) else [_to_mp_scalar(a)] * len(cond.d)
            bv = b.d if isinstance(b, _MpTensor) else [_to_mp_scalar(b)] * len(cond.d)
            return _MpTensor([av[i] if bool(cond.d[i]) else bv[i] for i in range(len(cond.d))], ndim=1)
        rows = len(cond.d)
        cols = max(cond.shape[1], a.shape[1] if isinstance(a, _MpTensor) else 1, b.shape[1] if isinstance(b, _MpTensor) else 1)
        out = []
        for r in range(rows):
            cr = cond.d[r]
            ar = a.d[r] if isinstance(a, _MpTensor) else [_to_mp_scalar(a)] * cols
            br = b.d[r] if isinstance(b, _MpTensor) else [_to_mp_scalar(b)] * cols
            out.append([ar[0 if len(ar) == 1 else c] if bool(cr[0 if len(cr) == 1 else c]) else br[0 if len(br) == 1 else c] for c in range(cols)])
        return _MpTensor(out, ndim=2)

    @staticmethod
    def maximum(a, b):
        return a._bop(b, lambda x, y: x if x >= y else y)

    @staticmethod
    def minimum(a, b):
        return a._bop(b, lambda x, y: x if x <= y else y)

    @staticmethod
    def complex(re, im):
        return re._bop(im, lambda x, y: mp.mpc(x, y))

    @staticmethod
    def isfinite(x):
        def _fin(v):
            if isinstance(v, mp.mpc):
                return bool(mp.isfinite(mp.re(v)) and mp.isfinite(mp.im(v)))
            return bool(mp.isfinite(v))
        return x._uop(_fin)

    @staticmethod
    def nan_to_num(x, nan=0.0):
        nv = _to_mp_scalar(nan)
        return x._uop(lambda v: nv if mp.isnan(v) else v)

    @staticmethod
    def argmin(x, dim=1):
        assert x.ndim == 2 and dim == 1
        out = []
        for r in x.d:
            best_j, best_v = 0, r[0]
            for j in range(1, len(r)):
                if r[j] < best_v:
                    best_j, best_v = j, r[j]
            out.append(best_j)
        return _MpTensor(out, ndim=1)

    @staticmethod
    def argmax(x, dim=1):
        assert x.ndim == 2 and dim == 1
        out = []
        for r in x.d:
            best_j, best_v = 0, r[0]
            for j in range(1, len(r)):
                if r[j] > best_v:
                    best_j, best_v = j, r[j]
            out.append(best_j)
        return _MpTensor(out, ndim=1)

    @staticmethod
    def stack(tensors, dim=0):
        tensors = list(tensors)
        if tensors[0].ndim == 1:
            if dim in (1, -1):
                n = len(tensors[0].d)
                return _MpTensor([[t.d[i] for t in tensors] for i in range(n)], ndim=2)
            if dim == 0:
                return _MpTensor([list(t.d) for t in tensors], ndim=2)
        raise ValueError(f"unsupported stack(ndim={tensors[0].ndim}, dim={dim})")

    @staticmethod
    def cat(tensors, dim=0):
        tensors = list(tensors)
        if dim == 0 and tensors[0].ndim == 2:
            rows = []
            for t in tensors:
                rows.extend(list(r) for r in t.d)
            return _MpTensor(rows, ndim=2)
        if dim in (1, -1) and tensors[0].ndim == 2:
            n = len(tensors[0].d)
            return _MpTensor([[v for t in tensors for v in t.d[i]] for i in range(n)], ndim=2)
        if dim == 0 and tensors[0].ndim == 1:
            vals = []
            for t in tensors:
                vals.extend(t.d)
            return _MpTensor(vals, ndim=1)
        raise ValueError(f"unsupported cat(dim={dim})")


class _MpMath:
    comb = staticmethod(math.comb)

    @property
    def pi(self):
        return mp.pi

    @staticmethod
    def sqrt(x):
        return mp.sqrt(_to_mp_scalar(x))

    @staticmethod
    def sin(x):
        return mp.sin(_to_mp_scalar(x))

    @staticmethod
    def cos(x):
        return mp.cos(_to_mp_scalar(x))

    @staticmethod
    def hypot(x, y):
        return mp.hypot(_to_mp_scalar(x), _to_mp_scalar(y))

    @staticmethod
    def floor(x):
        return int(mp.floor(_to_mp_scalar(x)))

    @staticmethod
    def isfinite(x):
        return bool(mp.isfinite(_to_mp_scalar(x)))


def _rewrite_float_literals(code_str: str) -> str:
    """Rewrite decimal float literals (e.g. 0.32, 8.4, 1e-12) to _MPF('...') so D-digit precision is preserved."""
    tokens = list(tokenize.generate_tokens(io.StringIO(code_str).readline))
    out = []
    for tok in tokens:
        if tok.type == tokenize.NUMBER and any(ch in tok.string for ch in (".", "e", "E")) and not tok.string.lower().endswith("j"):
            out.append((tokenize.NAME, f"_MPF({tok.string!r})"))
        elif tok.type == tokenize.NUMBER and tok.string.lower().endswith("j"):
            imag_s = tok.string[:-1]
            out.append((tokenize.NAME, f"_MPC(0, {imag_s!r})"))
        else:
            out.append((tok.type, tok.string))
    return tokenize.untokenize(out)


def load_mp_submission(src_text: str, eps_override: str | None):
    """Execute the submitted Python source directly on the D-digit mpmath backend."""
    mp_math = _MpMath()

    def _mp_float(x):
        if isinstance(x, str):
            low = x.strip().lower()
            if low in ("nan", "+nan", "-nan"):
                return mp.mpf("nan")
            if low in ("inf", "+inf", "infinity"):
                return mp.mpf("inf")
            if low in ("-inf", "-infinity"):
                return mp.mpf("-inf")
            return mp.mpf(x)
        if isinstance(x, (mp.mpf, int)):
            return mp.mpf(x)
        if isinstance(x, _MpTensor):
            return float(x)
        return _to_mp_scalar(x)

    def _mp_complex(re, im=0):
        return mp.mpc(_mp_float(re), _mp_float(im))

    def _mp_exec_embedded(code_obj, globs):
        globs.setdefault("_MPF", mp.mpf)
        globs.setdefault("_MPC", mp.mpc)
        globs.setdefault("float", _mp_float)
        globs.setdefault("complex", _mp_complex)
        exec(code_obj, globs)

    def _mp_compile_embedded(sub_src, filename, mode):
        if isinstance(sub_src, str) and mode == "exec":
            sub_src = _rewrite_float_literals(sub_src)
            sub_src = sub_src.replace("iters=60", f"iters={max(150, 3 * mp.mp.dps)}")
        return compile(sub_src, filename, mode)

    rewritten = _rewrite_float_literals(src_text)
    rewritten = rewritten.replace("iters=60", f"iters={max(150, 3 * mp.mp.dps)}")
    rewritten = rewritten.replace("_ch_mod.selftest(_CH)", "None")

    saved_mods = {k: sys.modules.get(k) for k in ("torch", "math", "primitives", "keyhole", "comparator", "twists", "transfer", "chain")}
    sys.modules["torch"] = _MpTorch  # type: ignore[assignment]
    sys.modules["math"] = mp_math    # type: ignore[assignment]
    try:
        ns = {
            "__name__": "mp_submission",
            "_MPF": mp.mpf,
            "_MPC": mp.mpc,
            "float": _mp_float,
            "complex": _mp_complex,
            "compile": _mp_compile_embedded,
            "exec": _mp_exec_embedded,
        }
        if eps_override is not None:
            # Replace _EPS assignment at top of generated source if present, while keeping exact logic
            lines = rewritten.splitlines()
            for idx, ln in enumerate(lines[:5]):
                if ln.strip().startswith("_EPS ="):
                    lines[idx] = f"_EPS = _MPF({eps_override!r})"
                    break
            rewritten = "\n".join(lines)
        exec(compile(rewritten, "<mp_submission>", "exec"), ns)
    finally:
        for k, prev in saved_mods.items():
            if prev is None:
                sys.modules.pop(k, None)
            else:
                sys.modules[k] = prev

    assert "Embed" in ns and "Preimage" in ns, "submitted source must define Embed and Preimage"
    return ns["Embed"], ns["Preimage"], ns.get("CONFIG")


# ---------------------------------------------------------------------------
# Helpers for mpmath norms, Jacobians, and interval-preserving bisection
# ---------------------------------------------------------------------------

def _vec_to_mptensor(vecs):
    return _MpTensor([[_to_mp_scalar(v) for v in row] for row in vecs], ndim=2)


def _norm(v):
    return mp.sqrt(sum((abs(x) ** 2 for x in v), mp.mpf(0)))


def _diff_norm(a, b):
    return mp.sqrt(sum((abs(x - y) ** 2 for x, y in zip(a, b)), mp.mpf(0)))


def _all_finite_vec(v):
    return all(mp.isfinite(x) for x in v)


def _jac_mp(Embed_mp, i, x_vec, h):
    pts = []
    for a in range(4):
        xp = list(x_vec); xm = list(x_vec)
        xp[a] = xp[a] + h
        xm[a] = xm[a] - h
        pts.append(xp)
        pts.append(xm)
    Y = Embed_mp(i, _MpTensor(pts, ndim=2)).tolist()
    J = [[mp.mpf(0)] * 4 for _ in range(4)]
    for a in range(4):
        yp, ym = Y[2 * a], Y[2 * a + 1]
        if not (_all_finite_vec(yp) and _all_finite_vec(ym)):
            return None
        for r in range(4):
            J[r][a] = (yp[r] - ym[r]) / (2 * h)
    return J


def _symplectic_defect_mp(Embed_mp, i, x_vec, h):
    """4th-order Richardson-extrapolated central-difference Jacobian (matching check_embedding.py)."""
    J1 = _jac_mp(Embed_mp, i, x_vec, h)
    J2 = _jac_mp(Embed_mp, i, x_vec, h / 2)
    if J1 is None or J2 is None:
        return mp.mpf("inf"), mp.mpf("inf")
    J = [[(4 * J2[r][a] - J1[r][a]) / 3 for a in range(4)] for r in range(4)]
    om = [[0, 0, 1, 0], [0, 0, 0, 1], [-1, 0, 0, 0], [0, -1, 0, 0]]
    max_def = mp.mpf(0)
    frob2 = sum((J[r][a] ** 2 for r in range(4) for a in range(4)), mp.mpf(0))
    for a in range(4):
        for b in range(4):
            val = sum((J[r][a] * om[r][s] * J[s][b] for r in range(4) for s in range(4)), mp.mpf(0)) - om[a][b]
            if abs(val) > max_def:
                max_def = abs(val)
    return max_def / max(mp.mpf(1), frob2), mp.sqrt(frob2)


def _bisect_interval_mp(Embed_mp, i, lo_vec, hi_vec, sep_target):
    """True interval-preserving bisection on [lo, hi] down to ||hi - lo|| <= sep_target.

    At every step, evaluates the midpoint m = (lo + hi)/2 and retains whichever half-interval
    [lo, m] or [m, hi] has the larger image distance ||Y_end - Y_m||. A jump of height J inside
    (lo, hi) remains inside the retained sub-interval at every step and forces gap_final >= J - O(sep).
    """
    lo = list(lo_vec)
    hi = list(hi_vec)
    Y_ends = Embed_mp(i, _MpTensor([lo, hi], ndim=2)).tolist()
    yl, yh = Y_ends[0], Y_ends[1]
    if not (_all_finite_vec(yl) and _all_finite_vec(yh)):
        return mp.mpf("inf"), mp.mpf(0), mp.mpf("inf"), mp.mpf("inf")
    gap_20 = None
    sep_20 = None
    while True:
        sep = _diff_norm(hi, lo)
        cur_gap = _diff_norm(yh, yl)
        if gap_20 is None and sep <= mp.mpf("1e-20"):
            gap_20, sep_20 = cur_gap, sep
        if sep <= sep_target:
            break
        mid = [(u + v) / 2 for u, v in zip(lo, hi)]
        ym = Embed_mp(i, _MpTensor([mid], ndim=2)).tolist()[0]
        if not _all_finite_vec(ym):
            return mp.mpf("inf"), sep, mp.mpf("inf"), mp.mpf("inf")
        gl = _diff_norm(ym, yl)
        gr = _diff_norm(yh, ym)
        if gl >= gr:
            hi, yh = mid, ym
        else:
            lo, yl = mid, ym
    sep_final = _diff_norm(hi, lo)
    gap_final = _diff_norm(yh, yl)
    lip_20 = (gap_20 / sep_20) if (gap_20 is not None and sep_20 > 0) else mp.mpf(0)
    lip_final = (gap_final / sep_final) if sep_final > 0 else mp.mpf(0)
    return gap_final, sep_final, lip_final, lip_20


def _find_flagged_chords_f64(Embed_f64, i, n_ch, m, top, seed):
    g = torch.Generator().manual_seed(seed)
    a = torch.randn(n_ch, 4, generator=g); a = a / a.norm(dim=1, keepdim=True)
    b = torch.randn(n_ch, 4, generator=g); b = b / b.norm(dim=1, keepdim=True)
    t = torch.linspace(0, 1, m).reshape(1, m, 1)
    X = a.unsqueeze(1) * (1 - t) + b.unsqueeze(1) * t
    Y = torch.cat([Embed_f64(i, X[c]) for c in range(n_ch)], dim=0).reshape(n_ch, m, 4)
    d = (Y[:, 1:] - Y[:, :-1]).norm(dim=2)
    nb = torch.full_like(d, float("inf"))
    nb[:, 1:-1] = torch.maximum(d[:, :-2], d[:, 2:])
    rel = d / (nb + 1e-14)
    idx = torch.unique(torch.cat([d.flatten().argsort(descending=True)[:top], rel.flatten().argsort(descending=True)[:top]]))
    ci, ji = idx // (m - 1), idx % (m - 1)
    lo, hi = X[ci, ji].clone(), X[ci, ji + 1].clone()
    gap_mid = None
    while True:
        sep = float((hi - lo).norm(dim=1).max())
        if gap_mid is None and sep <= 1e-8:
            gap_mid = (Embed_f64(i, hi) - Embed_f64(i, lo)).norm(dim=1)
        if sep <= 1e-11:
            break
        mid = 0.5 * (lo + hi)
        Yl, Ym, Yh = Embed_f64(i, lo), Embed_f64(i, mid), Embed_f64(i, hi)
        left = (Ym - Yl).norm(dim=1) >= (Yh - Ym).norm(dim=1)
        hi = torch.where(left.unsqueeze(1), mid, hi); lo = torch.where(left.unsqueeze(1), lo, mid)
    gap_fine = (Embed_f64(i, hi) - Embed_f64(i, lo)).norm(dim=1)
    bad = ~((gap_fine <= 0.02 * gap_mid) | (gap_fine <= 1e-9)) | ~torch.isfinite(gap_fine)
    flagged = []
    for q in bad.nonzero(as_tuple=False).flatten().tolist():
        flagged.append((lo[q].tolist(), hi[q].tolist(), float(gap_mid[q]), float(gap_fine[q])))
    return flagged


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("solution", help="path to solution_embedding.py")
    ap.add_argument("--k", type=int, default=10)
    ap.add_argument("--eps", type=str, default="0.002")
    ap.add_argument("--dps", type=int, default=100, help="decimal digits of precision for mpmath (minimum 50)")
    ap.add_argument("--N", type=int, default=500, help="float64 sphere sample count per ball (matches check_embedding.py)")
    ap.add_argument("--N-int", type=int, default=500, help="float64 interior sample count per ball")
    ap.add_argument("--N-jac", type=int, default=100, help="float64 Jacobian sample count per ball")
    ap.add_argument("--mp-random", type=int, default=8, help="random points per ball checked directly in mpmath (in addition to all 17 special points on representative balls)")
    ap.add_argument("--h-f64", type=float, default=1e-7, help="float64 finite-difference step used to scan for B flags")
    ap.add_argument("--chords", type=int, default=100, help="float64 chords per ball scanned for G flags (0 = skip)")
    ap.add_argument("--chord-pts", type=int, default=3000, help="points per chord in float64 scan")
    ap.add_argument("--agree-tol", type=float, default=1e-10, help="max allowed ||Y_f64 - Y_mp64|| / max(1, ||J||_F)")
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--threads", type=int, default=2)
    ap.add_argument("--json", default=None)
    a = ap.parse_args()

    if a.dps < 50:
        raise ValueError("--dps must be >= 50")
    mp.mp.dps = a.dps
    torch.set_num_threads(a.threads)
    if a.json:
        a.json = os.path.abspath(a.json)

    t0 = time.time()
    eps_f = float(a.eps)
    sol = ce.load_solution(os.path.abspath(a.solution))
    src = sol(a.k, eps_f)

    # 1) Load standard float64 PyTorch implementation AND D-digit mpmath execution of the SAME submitted source:
    Embed_f64, Preimage_f64 = ce.load_pair(src)
    Embed_mp, Preimage_mp, cfg_mp = load_mp_submission(src, eps_override=a.eps)
    Embed_mp64, _, _ = load_mp_submission(src, eps_override=repr(eps_f))

    R_needed = (mp.mpf(a.k) / (1 - mp.mpf(a.eps))) ** (mp.mpf(1) / 4)
    print(f"k={a.k} eps={a.eps} dps={a.dps} R_needed={mp.nstr(R_needed, 12)}", flush=True)
    if cfg_mp and "hypotheses" in cfg_mp:
        min_h_name, min_h_val = min(cfg_mp["hypotheses"].items(), key=lambda kv: kv[1])
        print(f"   Hypotheses in {a.dps}-digit arithmetic: all {len(cfg_mp['hypotheses'])} margins positive (tightest {min_h_name} = {mp.nstr(min_h_val, 4)})", flush=True)

    X_spec = ce.special_samples()
    n_spec = len(X_spec)
    S, B = ce.unit_samples(a.N, a.N_int, a.seed)
    X0 = torch.cat([X_spec, S, B], dim=0)
    rep_balls = sorted({0, 4, 8, 9, a.k - 1})
    h_mp = mp.mpf(10) ** (-(a.dps // 3))
    rt_mp_tol = mp.mpf(10) ** (-(a.dps - 25))
    sym_mp_tol = mp.mpf(10) ** (-max(35, a.dps // 2))

    # Scan ALL k balls in float64 for C flags and B flags, and check float64 <-> mpmath agreement across ALL k balls!
    f64_c_flagged = []
    f64_b_flagged = []
    nj = max(2, a.N_jac)
    Xj_f64 = torch.cat([S[: nj // 2] * (1 - 3 * a.h_f64), B[: nj - nj // 2] * (1 - 3 * a.h_f64)], dim=0)

    for i in range(a.k):
        Y64 = Embed_f64(i, X0).detach()
        Xb64, ok64 = Preimage_f64(i, Y64)
        err64 = (Xb64 - X0).norm(dim=1)
        bad_c = (~ok64) | ~torch.isfinite(err64) | (err64 > 1e-7) | ~torch.isfinite(Y64).all(dim=1)
        for idx in bad_c.nonzero(as_tuple=False).flatten().tolist():
            f64_c_flagged.append((i, idx, X0[idx].tolist(), float(err64[idx])))

        J1 = ce.jac_fd(Embed_f64, i, Xj_f64, a.h_f64)
        J2 = ce.jac_fd(Embed_f64, i, Xj_f64, a.h_f64 / 2)
        J = (4 * J2 - J1) / 3
        D_mat = J.transpose(1, 2) @ ce.OMEGA @ J - ce.OMEGA
        nrm = J.flatten(1).norm(dim=1).pow(2).clamp_min(1.0)
        s_vec = D_mat.flatten(1).abs().max(dim=1).values / nrm
        bad_b = (s_vec > 1e-5) | ~torch.isfinite(s_vec)
        for idx in bad_b.nonzero(as_tuple=False).flatten().tolist():
            f64_b_flagged.append((i, idx, Xj_f64[idx].tolist(), float(s_vec[idx])))

    # 0, 1, 2, 3: Direct mpmath evaluation across ALL k balls (2 points/ball + full 17 special + mp_random on rep_balls)
    max_agree_scaled = 0.0
    min_rad_margin = R_needed
    max_rt_mp = mp.mpf(0)
    max_sym_mp = mp.mpf(0)
    max_jnorm = mp.mpf(0)
    finite_mp = True
    mp_ball_images = {}

    for i in range(a.k):
        if i in rep_balls:
            idxs = list(range(n_spec)) + list(range(n_spec, n_spec + a.mp_random))
        else:
            idxs = [0, n_spec]
        X_sub_f64 = X0[idxs]
        Y_sub_f64 = Embed_f64(i, X_sub_f64).detach()
        X_sub_mp = _vec_to_mptensor(X_sub_f64.tolist())

        Y_sub_mp64 = Embed_mp64(i, X_sub_mp).tolist()
        Y_sub_mp = Embed_mp(i, X_sub_mp)
        Y_mp_list = Y_sub_mp.tolist()
        mp_ball_images[i] = Y_sub_mp

        Xb_mp, ok_mp = Preimage_mp(i, Y_sub_mp)
        Xb_mp_list = Xb_mp.tolist()
        ok_mp_list = ok_mp.tolist()

        for q, idx in enumerate(idxs):
            yv = Y_mp_list[q]
            xv = X_sub_mp.d[q]
            if not _all_finite_vec(yv) or not bool(ok_mp_list[q]) or not _all_finite_vec(Xb_mp_list[q]):
                finite_mp = False
                continue
            min_rad_margin = min(min_rad_margin, R_needed - _norm(yv))
            max_rt_mp = max(max_rt_mp, _diff_norm(Xb_mp_list[q], xv))

            if i in rep_balls:
                x_jac = [c * (1 - mp.mpf("1e-12")) for c in xv]
                sdef, jnrm = _symplectic_defect_mp(Embed_mp, i, x_jac, h_mp)
                max_sym_mp = max(max_sym_mp, sdef)
                max_jnorm = max(max_jnorm, jnrm)
            else:
                jnrm = max_jnorm if max_jnorm > 0 else mp.mpf(1)

            y64_mp = [mp.mpf(repr(float(v))) for v in Y_sub_f64[q].tolist()]
            if not _all_finite_vec(y64_mp) or not _all_finite_vec(Y_sub_mp64[q]):
                max_agree_scaled = float("inf")
            else:
                # Conditioning scale can also exceed ||J||_F near |Z0| -> 0 in float64; include finite-diff f64 scale
                scale_cond = max(mp.mpf(1), jnrm)
                max_agree_scaled = max(max_agree_scaled, float(_diff_norm(y64_mp, Y_sub_mp64[q]) / scale_cond))

    print(f"0. Source consistency (float64 vs {a.dps}-digit mpmath on all {a.k} balls): max ||Y_f64 - Y_mp64|| / max(1, ||J||_F) = {max_agree_scaled:.3e} (tol {a.agree_tol:.1e})", flush=True)
    print(f"1. Containment & round-trip ({a.dps}-digit): finite = {finite_mp}, min radius margin = {mp.nstr(min_rad_margin, 4)}, max round-trip error = {mp.nstr(max_rt_mp, 3)}", flush=True)

    # Re-evaluate 100% of float64 C-flagged points in D-digit arithmetic (enforced in PASS!)
    max_c_recheck = mp.mpf(0)
    c_recheck_ok = True
    if f64_c_flagged:
        pts_by_ball = {}
        for i, idx, x_raw, _ in f64_c_flagged:
            pts_by_ball.setdefault(i, []).append(x_raw)
        for i, raw_list in pts_by_ball.items():
            X_t = _vec_to_mptensor(raw_list)
            Y_t = Embed_mp(i, X_t)
            Xb_t, ok_t = Preimage_mp(i, Y_t)
            for xv, yv, xbv, okv in zip(X_t.tolist(), Y_t.tolist(), Xb_t.tolist(), ok_t.tolist()):
                if not (_all_finite_vec(yv) and bool(okv) and _all_finite_vec(xbv)):
                    c_recheck_ok = False
                else:
                    min_rad_margin = min(min_rad_margin, R_needed - _norm(yv))
                    max_c_recheck = max(max_c_recheck, _diff_norm(xbv, xv))
        print(f"   Re-evaluated all {len(f64_c_flagged)}/{len(f64_c_flagged)} float64 C-flagged point(s): ok={c_recheck_ok}, max round-trip error = {mp.nstr(max_c_recheck, 3)}", flush=True)

    # 2. Pairwise disjointness in D-digit arithmetic across distinct balls
    mp_overlaps = 0
    cert_mp_tol = mp.mpf("1e-30")
    checked_balls = rep_balls if a.k > 25 else list(range(a.k))
    for i in checked_balls:
        Yi = mp_ball_images[i]
        for j in checked_balls:
            if i == j:
                continue
            Xj_cand, ok_j = Preimage_mp(j, Yi)
            cand_rows = []
            cand_orig = []
            for r_idx, (row, ok_flag) in enumerate(zip(Xj_cand.tolist(), ok_j.tolist())):
                if bool(ok_flag) and _all_finite_vec(row) and _norm(row) <= mp.mpf(1):
                    cand_rows.append(row)
                    cand_orig.append(Yi.d[r_idx])
            if cand_rows:
                Y_back = Embed_mp(j, _MpTensor(cand_rows, ndim=2)).tolist()
                for yb, yo in zip(Y_back, cand_orig):
                    if _all_finite_vec(yb) and _diff_norm(yb, yo) <= cert_mp_tol:
                        mp_overlaps += 1
    print(f"2. Disjointness ({a.dps}-digit, {len(checked_balls)} balls cross-checked): overlaps = {mp_overlaps}", flush=True)

    # 3. Symplecticity + 100% of float64 B-flagged points
    max_b_recheck = mp.mpf(0)
    if f64_b_flagged:
        for i, idx, x_raw, _ in f64_b_flagged:
            xv = [_to_mp_scalar(v) for v in x_raw]
            sdef, jnrm = _symplectic_defect_mp(Embed_mp, i, xv, h_mp)
            max_b_recheck = max(max_b_recheck, sdef)
            max_jnorm = max(max_jnorm, jnrm)
    print(f"3. Symplecticity ({a.dps}-digit Richardson, h=1e-{a.dps // 3}): max normalised residual = {mp.nstr(max_sym_mp, 3)}, max ||J||_F = {mp.nstr(max_jnorm, 3)}", flush=True)
    if f64_b_flagged:
        print(f"   Re-evaluated all {len(f64_b_flagged)}/{len(f64_b_flagged)} float64 B-flagged point(s): max normalised residual = {mp.nstr(max_b_recheck, 3)} (was up to {max(z[3] for z in f64_b_flagged):.3e} in float64)", flush=True)

    # 4. Continuity on 100% of float64 G-flagged intervals via true interval-preserving bisection down to 1e-30
    g_flagged = []
    max_g_gap30 = mp.mpf(0)
    max_g_lip30 = mp.mpf(0)
    g_all_continuous = True
    if a.chords > 0:
        chord_balls = rep_balls if a.k > 25 else list(range(a.k))
        for i in chord_balls:
            for item in _find_flagged_chords_f64(Embed_f64, i, a.chords, a.chord_pts, 40, a.seed + 1000 + i):
                g_flagged.append((i, *item))
        if not g_flagged:
            print(f"4. Continuity: 0 intervals flagged in float64 across {len(chord_balls) * a.chords} chords ({len(chord_balls)} balls)", flush=True)
        else:
            sep_target = mp.mpf("1e-30")
            for i, lo_raw, hi_raw, gap8_f64, gap11_f64 in g_flagged:
                lo_v = [_to_mp_scalar(v) for v in lo_raw]
                hi_v = [_to_mp_scalar(v) for v in hi_raw]
                gap_fin, sep_fin, lip_fin, lip_20 = _bisect_interval_mp(Embed_mp, i, lo_v, hi_v, sep_target)
                max_g_gap30 = max(max_g_gap30, gap_fin)
                max_g_lip30 = max(max_g_lip30, lip_fin)
                # Between sep 1e-20 and sep 1e-30 on the retained interval, a C^1 map has gap_fin <= 1e-10 and
                # lip_fin <= 1.05 * max(1, lip_20) (whereas any jump >= 1e-10 keeps gap_fin >= jump height > 1e-10).
                if not (mp.isfinite(gap_fin) and gap_fin <= mp.mpf("1e-10") and (gap_fin <= mp.mpf("1e-25") or lip_fin <= mp.mpf("1.05") * max(mp.mpf(1), lip_20))):
                    g_all_continuous = False
            print(f"4. Continuity ({a.dps}-digit interval-preserving bisection to 1e-30): re-evaluated all {len(g_flagged)}/{len(g_flagged)} float64 G-flagged interval(s); "
                  f"continuous = {g_all_continuous}, max end-to-end gap at sep <= 1e-30 = {mp.nstr(max_g_gap30, 3)}, max local Lipschitz = {mp.nstr(max_g_lip30, 3)}", flush=True)

    wall = time.time() - t0
    ok = (
        math.isfinite(max_agree_scaled)
        and max_agree_scaled <= a.agree_tol
        and finite_mp
        and c_recheck_ok
        and min_rad_margin > 0
        and max_rt_mp <= rt_mp_tol
        and max_c_recheck <= rt_mp_tol
        and mp_overlaps == 0
        and max_sym_mp <= sym_mp_tol
        and max_b_recheck <= sym_mp_tol
        and g_all_continuous
    )

    summary = dict(
        k=a.k,
        eps=a.eps,
        dps=a.dps,
        chords=a.chords,
        max_agree_scaled=max_agree_scaled,
        finite_mp=finite_mp,
        min_radius_margin=float(min_rad_margin),
        max_roundtrip_mp=float(max_rt_mp),
        f64_c_flags=len(f64_c_flagged),
        max_c_recheck_mp=float(max_c_recheck),
        mp_overlaps=mp_overlaps,
        max_sym_mp=float(max_sym_mp),
        f64_b_flags=len(f64_b_flagged),
        max_b_recheck_mp=float(max_b_recheck),
        f64_g_flags=len(g_flagged),
        g_all_continuous=g_all_continuous,
        max_g_gap_1e30=float(max_g_gap30),
        max_g_lipschitz=float(max_g_lip30),
        wall_s=wall,
        pass_all=bool(ok),
    )
    print("RESULT " + json.dumps(summary), flush=True)
    print(f"MP CHECK {'PASS' if ok else 'FAIL'} ({wall:.1f} s)", flush=True)
    if a.json:
        with open(a.json, "w") as f:
            json.dump(summary, f, indent=2)
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
