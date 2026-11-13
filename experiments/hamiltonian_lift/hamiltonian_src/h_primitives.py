"""Autograd-safe C-infinity bump/step functions and Gauss-Legendre utilities in PyTorch."""
from __future__ import annotations

import math
import torch


def flat_step(x: torch.Tensor) -> torch.Tensor:
    """Autograd-safe C^inf flat step S(x) on R with S=0 on (-inf,0] and S=1 on [1,+inf).

    Uses the reflection identity S(x) = 1 - S(1 - x) on x >= 1/2 and safe interior
    clamping BEFORE evaluating 1/x and exp(...) so PyTorch backward never produces
    0 * inf = NaN at the boundary seams x <= 0 or x >= 1.
    """
    interior = (x > 1e-12) & (x < 1.0 - 1e-12)
    # Clamp strictly inside (0, 1) so inactive autograd branches remain finite
    xc = torch.clamp(x, min=1e-12, max=1.0 - 1e-12)
    # Use log-space difference delta = 1/(1-x) - 1/x; S(x) = sigmoid(delta) = 1/(1 + exp(-delta))
    # Note: -delta = 1/x - 1/(1-x). Clamping -delta to [-700, 700] avoids exp overflow cleanly!
    neg_delta = torch.clamp(1.0 / xc - 1.0 / (1.0 - xc), min=-700.0, max=700.0)
    s_in = 1.0 / (1.0 + torch.exp(neg_delta))
    return torch.where(interior, s_in, torch.where(x >= 1.0 - 1e-12, torch.ones_like(x), torch.zeros_like(x)))


def flat_step_jet(x: torch.Tensor) -> tuple[torch.Tensor, torch.Tensor, torch.Tensor]:
    """Return (S(x), S'(x), S''(x)) in an autograd-safe vectorized form."""
    interior = (x > 1e-12) & (x < 1.0 - 1e-12)
    xc = torch.clamp(x, min=1e-12, max=1.0 - 1e-12)
    omx = 1.0 - xc
    neg_delta = torch.clamp(1.0 / xc - 1.0 / omx, min=-700.0, max=700.0)
    s = 1.0 / (1.0 + torch.exp(neg_delta))
    # Use min(s, 1-s) via exp(-|neg_delta|) / (1 + exp(-|neg_delta|))^2 for catastrophic-cancellation-free S*(1-S)
    abs_d = torch.clamp(torch.abs(neg_delta), max=700.0)
    em = torch.exp(-abs_d)
    s_one_minus_s = em / ((1.0 + em) ** 2)

    kp = 1.0 / (xc * xc) + 1.0 / (omx * omx)
    kpp = -2.0 / (xc * xc * xc) + 2.0 / (omx * omx * omx)

    sp = s_one_minus_s * kp
    spp = s_one_minus_s * ((1.0 - 2.0 * s) * kp * kp + kpp)

    z = torch.zeros_like(x)
    s_out = torch.where(interior, s, torch.where(x >= 1.0 - 1e-12, torch.ones_like(x), z))
    sp_out = torch.where(interior, sp, z)
    spp_out = torch.where(interior, spp, z)
    return s_out, sp_out, spp_out


def flat_step_scalar(x: float, derivative: int = 0) -> float:
    """Fast scalar float64 evaluation of S(x), S'(x), or S''(x)."""
    if x <= 1e-13:
        return 0.0
    if x >= 1.0 - 1e-13:
        return 1.0 if derivative == 0 else 0.0
    omx = 1.0 - x
    neg_delta = 1.0 / x - 1.0 / omx
    if neg_delta > 700.0:
        return 0.0
    if neg_delta < -700.0:
        return 1.0 if derivative == 0 else 0.0
    s = 1.0 / (1.0 + math.exp(neg_delta))
    if derivative == 0:
        return s
    em = math.exp(-abs(neg_delta))
    prod = em / ((1.0 + em) ** 2)
    kp = 1.0 / (x * x) + 1.0 / (omx * omx)
    if derivative == 1:
        return prod * kp
    kpp = -2.0 / (x * x * x) + 2.0 / (omx * omx * omx)
    if derivative == 2:
        return prod * ((1.0 - 2.0 * s) * kp * kp + kpp)
    raise ValueError(f"Unsupported scalar derivative order: {derivative}")


def gauss_legendre_01(n: int = 32) -> tuple[torch.Tensor, torch.Tensor]:
    """Return (nodes, weights) of n-point Gauss-Legendre quadrature on [0, 1] in float64."""
    # Golub-Welsch tridiagonal eigenvalue algorithm in pure torch.float64
    idx = torch.arange(1, n, dtype=torch.float64)
    beta = idx / torch.sqrt(4.0 * idx * idx - 1.0)
    J = torch.diag(beta, 1) + torch.diag(beta, -1)
    evals, evecs = torch.linalg.eigh(J)
    nodes = 0.5 * (evals + 1.0)
    weights = evecs[0, :] ** 2
    return nodes, weights
