import SymplecticPacking.HighDim.Comparator.Poly
import SymplecticPacking.Branch2.Planar.Well
import SymplecticPacking.Qhat.InnerFamily
import SymplecticPacking.Qhat.Ham

/-!
# The planar generator of the parameterised rearrangement

Explicit construction of `RealiseGen.planarGen`. The input (`Input`) is a family of affine pieces
`v ↦ a_r(y) + b_r(y) v` (`f_y = max_r`), uniform bounds `L ≥ |b_r|`, `M ≥ |a_r| + |b_r|` on the
support of a parameter cutoff `ψ`, the number `n` of pieces and the tolerance `ξ`. Every constant
below is a closed formula in `(n, ξ, L, M)` and so is the *same for every parameter `y`*; only
the functions explicitly indexed by `y` vary with `y`. The construction is the one
in the form already formalised for a single slice in `Branch2/Planar` and `Qhat`:

1. (§2) log-sum-exp potential `U₀_y`, endpoint barrier `U_y = U₀_y + κ(1/v + 1/(1-v))`, angular
   wall `V(θ) = νθ²/(1/4 - θ²)`, with `η, β, σ, ν, κ` explicit (`h = 1`, `e = ξ`);
2. (§3) the critical point `v_*(y)` (definite description), the exactly quadratic modification
   with the *uniform* width `ε_U` (in place of the per-slice `Well.eps`, which uses a supremum),
   and the signed Morse inverses `X_U(y)`, `X_V` (`X_V` is the `Branch2` well of `V`, independent
   of `y`); both are linear near `0`, so the densities below are flat at the origin;
3. (§4–5) the interpolated density family `J_{y,s} = X_{y,s}' Y_s'`, the rotation/area
   normalisation `f_{y,s} = F_{y,s} ∘ T⁻¹ ∘ D` (`Inner.TrotInv`, `Inner.Darea`), the rescaled
   polar charts `C_{y,λ}` (closed form of `b_y + ∫₀¹ DC_y(tλw) w dt`, as `Qhat.Clam`) and the clock
   `λ(s)`; the inner family `q_{y,s} = C_{y,λ(s)} ∘ f_{y,s}`;
4. (§6) the five-segment ordinary path with the uniform shrink factor `c_new` and uniform support
   level `P_supp`, packaged as a `Qhat.PathData`;
5. (§6–7) the whole-path area normalisation, its flow and the source primitive are the generic
   `Qhat.Qham` (convention `ι_X ω = -dQ`);
6. the parameter cutoff: `B(y, s, w) = ψ(y) Q_y(ψ(y) s, w)`, whose time-one map is the time-`ψ(y)`
   map of `Q_y` (the identity where `ψ = 0`, the full rearrangement where `ψ = 1`).

`sliceInput` instantiates the input for the normalised slice family `F(y, ℓ(y) v)` of a polytope.
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen

open Set Complex
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff Real

variable {m q : ℕ}

/-- Input of the parameterised planar construction. -/
structure Input (m : ℕ) where
  /-- the affine pieces `(a_r(y), b_r(y))` of `f_y(v) = max_r (a_r(y) + b_r(y) v)` -/
  pieces : Moments m → List (ℝ × ℝ)
  /-- the number of pieces -/
  n : ℕ
  /-- the planar tolerance `ξ` -/
  xi : ℝ
  /-- uniform slope bound `L ≥ |b_r(y)|` on the support of `cutoff` -/
  L : ℝ
  /-- uniform value bound `M ≥ |a_r(y)| + |b_r(y)|` on the support of `cutoff` -/
  M : ℝ
  /-- the parameter cutoff `ψ` (one on the parameter compact, zero off its buffer) -/
  cutoff : Moments m → ℝ

namespace Input

variable (D : Input m)

/-! ### §2 constants and potentials (`h = 1`, `e = ξ`) -/

/-- `η = min(1/16, ξ/(32(L+1)))/2`. -/
def eta : ℝ := min (1 / 16) (D.xi / (32 * (D.L + 1))) / 2

/-- `σ = ξ/8`. -/
def sig : ℝ := D.xi / 8

/-- `β = η/8`. -/
def beta : ℝ := D.eta / 8

/-- `ν = 4σβ(1-β)`. -/
def nu : ℝ := 4 * D.sig * D.beta * (1 - D.beta)

/-- `κ = ση/8`. -/
def kappa : ℝ := D.sig * D.eta / 8

/-- The quadratic-modification tolerance `δ = ξ/64`. -/
def tol : ℝ := D.xi / 64

/-- The log-sum-exp inverse temperature `c = 8(n+1)/σ > 4n/σ`. -/
def clse : ℝ := 8 * (D.n + 1) / D.sig

/-- The smooth convex majorant `U₀_y(v) = c⁻¹ log Σ_r exp(c(a_r(y) + b_r(y) v))`. -/
def U0 (y : Moments m) (v : ℝ) : ℝ :=
  D.clse⁻¹ * Real.log (((D.pieces y).map fun p => Real.exp (D.clse * (p.1 + p.2 * v))).sum)

/-- The proper potential `U_y(v) = U₀_y(v) + κ(1/v + 1/(1-v))` on `(0, 1)`. -/
def U (y : Moments m) (v : ℝ) : ℝ := D.U0 y v + D.kappa * (1 / v + 1 / (1 - v))

/-- The angular wall `V(θ) = νθ²/(1/4 - θ²)` on `(-1/2, 1/2)`. -/
def V (θ : ℝ) : ℝ := D.nu * θ ^ 2 / (1 / 4 - θ ^ 2)

/-! ### §3 uniform Morse constants -/

/-- `r₀ = min(1/8, √(κ/(4(L + 2κ + 1))))`, so `κ/r₀² > 2(L + 2κ)` and `r₀ < v_* < 1 - r₀`. -/
def r0 : ℝ := min (1 / 8) √(D.kappa / (4 * (D.L + 2 * D.kappa + 1)))

/-- Upper bound `cL² + 4κ/r₀³` for `U_y''(v_*)`. -/
def alphaMax : ℝ := D.clse * D.L ^ 2 + 4 * D.kappa / D.r0 ^ 3

/-- Lower bound `32κ` for `U_y''`. -/
def alphaMin : ℝ := 32 * D.kappa

/-- Bound `8c²L³ + 192κ/r₀⁴ + 1` for `|U_y'''|` on `[r₀/2, 1 - r₀/2]`. -/
def K3max : ℝ := 8 * D.clse ^ 2 * D.L ^ 3 + 192 * D.kappa / D.r0 ^ 4 + 1

/-- The uniform width of the quadratic modification,
`ε_U = min(r₀/8, α_min/(32 K₃ (1 + C_ψ)), √(δ/α_max))`. -/
def epsU : ℝ :=
  min (min (D.r0 / 8) (D.alphaMin / (32 * D.K3max * (1 + Inner.Cpsi)))) √(D.tol / D.alphaMax)

open Classical in
/-- The critical point `v_*(y)` of `U_y` in `(0, 1)` (the unique one); `1/2` if there is none. -/
def vstar (y : Moments m) : ℝ :=
  if h : ∃! v, v ∈ Ioo (0 : ℝ) 1 ∧ deriv (D.U y) v = 0 then Explicit.the h else 1 / 2

/-- `α_y = U_y''(v_*)`. -/
def alphaU (y : Moments m) : ℝ := deriv (deriv (D.U y)) (D.vstar y)

/-- `g_y(x) = U_y(v_* + x) - U_y(v_*)`. -/
def gU (y : Moments m) (x : ℝ) : ℝ := D.U y (D.vstar y + x) - D.U y (D.vstar y)

/-- `g_c(x) = α_y x²/2 - g_y(x)`. -/
def gcU (y : Moments m) (x : ℝ) : ℝ := D.alphaU y * x ^ 2 / 2 - D.gU y x

/-- The exactly quadratic modification `f̃_y = g_y + ψ(x/ε_U) g_c`. -/
def ftU (y : Moments m) (x : ℝ) : ℝ := D.gU y x + Inner.psiR (x / D.epsU) * D.gcU y x

/-- `Σ_y(x) = sign(x) √f̃_y(x)`. -/
def SigU (y : Moments m) (x : ℝ) : ℝ := Real.sign x * √(D.ftU y x)

/-- `θ_y(t) = (1 - 2v_*)/2 + t/(2√(1+t²))`, a diffeomorphism `ℝ → (-v_*, 1 - v_*)`. -/
def thetaU (y : Moments m) (t : ℝ) : ℝ := (1 - 2 * D.vstar y) / 2 + 1 / 2 * (t / √(1 + t ^ 2))

/-- The signed Morse inverse `X_U(y) = θ_y ∘ (Σ_y ∘ θ_y)⁻¹`, linear near `0`. -/
def XU (y : Moments m) (u : ℝ) : ℝ :=
  D.thetaU y (Inner.invR (fun t => D.SigU y (D.thetaU y t)) u)

/-- `a₀(y) = X_U(y)'(0) = √(2/α_y)`. -/
def a0 (y : Moments m) : ℝ := √(2 / D.alphaU y)

/-- The angular well (independent of `y`). -/
def wellV : Branch2.Planar.Well := ⟨D.V, -(1 / 2), 1 / 2, 0, D.tol⟩

/-- The angular Morse inverse `X_V`, linear near `0`. -/
def XV (v : ℝ) : ℝ := D.wellV.X v

/-- `b₀ = X_V'(0)`. -/
def b0 : ℝ := 1 / D.wellV.lin

/-! ### §5 uniform energy, margins and the clock -/

/-- `δ = η/8`. -/
def drect : ℝ := D.eta / 8

/-- `A_min = (1 - 2δ)²`. -/
def Amin : ℝ := (1 - 2 * D.drect) ^ 2

/-- The source-disk level `p† = 1 - 5η`. -/
def pdag : ℝ := 1 - 5 * D.eta

/-- Uniform modified-energy bound on the rectangle
`[δ, 1-δ] × [-1/2+δ, 1/2-δ]`; each quadratic modification costs at most `tol`. -/
def Erect : ℝ :=
  2 * D.M + 2 + 2 * D.kappa / D.drect + D.nu / (2 * D.drect) + 2 * D.tol

/-- `a_max = √(2/α_min)`, `a_min = √(2/α_max)`. -/
def amax : ℝ := √(2 / D.alphaMin)
def amin : ℝ := √(2 / D.alphaMax)

/-- `K_min = π a_min b₀`. -/
def Kmin : ℝ := π * D.amin * D.b0

/-- The common energy bound `Ē = E_rect + p† A_min/(K_min (A_min - p†)) + 1`. -/
def Ebar : ℝ := D.Erect + D.pdag * D.Amin / (D.Kmin * (D.Amin - D.pdag)) + 1

/-- Raw coordinate bounds `X̄ = a_max √Ē + 1`, `Ȳ = b₀ √Ē + 1/2`. -/
def Xbar : ℝ := D.amax * √D.Ebar + 1
def Ybar : ℝ := D.b0 * √D.Ebar + 1 / 2

/-- Radial barrier margin. The minimum of the endpoint barrier costs `4κ`, and
passing from the modified well back to the original well costs at most `tol`. -/
def dP : ℝ := D.kappa / (2 * D.M + 2 + 4 * D.kappa + D.Ebar + D.tol)

/-- Angular margin, including the error of the quadratic modification of the angular well. -/
def dTh : ℝ := (1 - √((D.Ebar + D.tol + 1) / (D.Ebar + D.tol + 1 + D.nu))) / 2

/-- `d_s = min(1/4, d_P/(2X̄), d_Θ/(2Ȳ))`. -/
def ds : ℝ := min (1 / 4) (min (D.dP / (2 * D.Xbar)) (D.dTh / (2 * D.Ybar)))

/-- `λ₀ = min(1/2, r₀/(2X̄), 1/(4Ȳ))`. -/
def lambda0 : ℝ := min (min (1 / 2) (D.r0 / (2 * D.Xbar))) (1 / (4 * D.Ybar))

/-- The clock `λ(s) = λ₀ S(2s) + (1 - λ₀) S((s - 1 + d_s)/d_s)`. -/
def lam (s : ℝ) : ℝ :=
  D.lambda0 * Real.smoothTransition (2 * s) +
    (1 - D.lambda0) * Real.smoothTransition ((s - 1 + D.ds) / D.ds)

/-! ### §4–5 the inner family -/

/-- `X_{y,s}(u) = (1-s) a₀(y) u + s X_U(y)(u)`. -/
def Xs (y : Moments m) (s u : ℝ) : ℝ := (1 - s) * D.a0 y * u + s * D.XU y u

/-- `Y_s(v) = (1-s) b₀ v + s X_V(v)`. -/
def Ys (s v : ℝ) : ℝ := (1 - s) * D.b0 * v + s * D.XV v

/-- The density `J_{y,s}(u, v) = X_{y,s}'(u) Y_s'(v)`. -/
def Js (y : Moments m) (s : ℝ) (w : ℂ) : ℝ :=
  ((1 - s) * D.a0 y + s * deriv (D.XU y) w.re) * ((1 - s) * D.b0 + s * deriv D.XV w.im)

/-- `F_{y,s} = (X_{y,s}, Y_s)`. -/
def Fs (y : Moments m) (s : ℝ) (w : ℂ) : ℂ := (D.Xs y s w.re : ℂ) + (D.Ys s w.im : ℂ) * I

/-- `f_{y,s} = F_{y,s} ∘ T_{y,s}⁻¹ ∘ D_{y,s}`. -/
def fs (y : Moments m) (s : ℝ) (z : ℂ) : ℂ :=
  D.Fs y s (Inner.TrotInv (D.Js y) s (Inner.Darea (D.Js y) s z))

/-- `r_b(y) = √(v_*/π)`. -/
def rb (y : Moments m) : ℝ := √(D.vstar y / π)

/-- `b_y = (-r_b(y), 0) = C_y(0)`. -/
def bpt (y : Moments m) : ℂ := -(D.rb y : ℂ)

/-- Angular factor `2π r_b i g(2πiλv)` of `C_{y,λ}`. -/
def Hy (y : Moments m) (lam : ℝ) (w : ℂ) : ℂ :=
  ((2 * π * D.rb y : ℝ) : ℂ) * I * Qhat.gexp (((2 * π * lam * w.im : ℝ) : ℂ) * I)

/-- Radial factor `e^{2πiλv}/(π(r_b + √((v_* + λu)/π)))` of `C_{y,λ}`. -/
def Hx (y : Moments m) (lam : ℝ) (w : ℂ) : ℂ :=
  (((π * (D.rb y + √((D.vstar y + lam * w.re) / π)))⁻¹ : ℝ) : ℂ) *
    Complex.exp (((2 * π * lam * w.im : ℝ) : ℂ) * I)

/-- The rescaled polar chart `C_{y,λ}(w) = b_y + ∫₀¹ DC_y(tλw) w dt`
(`C_y(x, θ) = -√((v_* + x)/π) e^{2πiθ}`), in closed form `b_y - v H_y - u H_x`. -/
def Clam (y : Moments m) (lam : ℝ) (w : ℂ) : ℂ :=
  D.bpt y - (w.im : ℂ) * D.Hy y lam w - (w.re : ℂ) * D.Hx y lam w

/-- The inner family `q_{y,s} = C_{y,λ(s)} ∘ f_{y,s}`. -/
def qin (y : Moments m) (s : ℝ) (z : ℂ) : ℂ := D.Clam y (D.lam s) (D.fs y s z)

/-- `j₀ = a₀ b₀`, `c_x = a₀/√j₀`, `c_y = b₀/√j₀`. -/
def j0 (y : Moments m) : ℝ := D.a0 y * D.b0
def cx (y : Moments m) : ℝ := D.a0 y / √(D.j0 y)
def cy (y : Moments m) : ℝ := D.b0 / √(D.j0 y)

/-- `A₀(y) = DC_y(0) diag(c_x, c_y) = diag(A₁₁, A₂₂)`. -/
def A11 (y : Moments m) : ℝ := -(D.cx y / (2 * π * D.rb y))
def A22 (y : Moments m) : ℝ := -(2 * π * D.rb y * D.cy y)

/-- `A₀(y) z`. -/
def A0 (y : Moments m) (z : ℂ) : ℂ :=
  ((D.A11 y * z.re : ℝ) : ℂ) + ((D.A22 y * z.im : ℝ) : ℂ) * I

/-- `M_{y,σ} = Rot_{πσ} diag(|A₁₁|^σ, |A₂₂|^σ)`. -/
def Msig (y : Moments m) (σ : ℝ) (z : ℂ) : ℂ :=
  Inner.Rot (π * σ) (((|D.A11 y| ^ σ * z.re : ℝ) : ℂ) + ((|D.A22 y| ^ σ * z.im : ℝ) : ℂ) * I)

/-! ### §6 uniform constants of the five segments -/

/-- `R† = √(p†/π)`, `R_h = √(1/π)`, `r_b^max = √((1 - r₀)/π)`. -/
def Rdag : ℝ := √(D.pdag / π)
def Rh : ℝ := √(1 / π)
def rbmax : ℝ := √((1 - D.r0) / π)

/-- Uniform bound `√(a_max/b₀)/(2√(πr₀)) + 2√π √(b₀/a_min)` for `|A₁₁|, |A₂₂|`. -/
def Amax : ℝ := √(D.amax / D.b0) / (2 * √(π * D.r0)) + 2 * √π * √(D.b0 / D.amin)

/-- `B₃ = R† (1 + A_max)`. -/
def B3 : ℝ := D.Rdag * (1 + D.Amax)

/-- Radial range `[P_min, P_max]` of the charts: `P_min = min(r₀, d_P)/4`, `P_max = 3/2`. -/
def Pmin : ℝ := min D.r0 D.dP / 4
def Pmax : ℝ := 3 / 2

/-- `M_C = 1/(2√(πP_min)) + 2√(πP_max)` bounds `‖DC_y‖` on the radial range. -/
def MC : ℝ := 1 / (2 * √(π * D.Pmin)) + 2 * √(π * Pmax)

/-- `B* = M_C √(X̄² + Ȳ²)` bounds `|q_{y,s} - b_y|`. -/
def Bstar : ℝ := D.MC * √(D.Xbar ^ 2 + D.Ybar ^ 2)

/-- `R_q = √((1 - d_P/2)/π)` bounds `|q_{y,1}|`. -/
def Rq : ℝ := √((1 - D.dP / 2) / π)

/-- The uniform shrink factor `c = min(1/4, (R_h - r_b^max)/(8 max(R†, B₃, B*)))`. -/
def cnew : ℝ := min (1 / 4) ((Rh - D.rbmax) / (8 * max D.Rdag (max D.B3 D.Bstar)))

/-- `R_supp = max(R†, r_b^max + c B₃, r_b^max + c B*, R_q)`. -/
def Rsupp : ℝ :=
  max (max D.Rdag (D.rbmax + D.cnew * D.B3)) (max (D.rbmax + D.cnew * D.Bstar) D.Rq)

/-- The uniform support level `P_supp = π R_supp²`. -/
def Psupp : ℝ := π * D.Rsupp ^ 2

/-! ### §6 the five-segment path -/

/-- The flat clock `σ_j(t) = S(5t - j)`. -/
def clock (j : ℕ) (t : ℝ) : ℝ := Real.smoothTransition (5 * t - j)

/-- The five segments (shrink, translate to `b_y`, linear deformation `M_{y,σ}`, inner family,
convex expansion from `b_y`), telescoped into one formula in the clocks. -/
def ordPath (y : Moments m) (t : ℝ) (z : ℂ) : ℂ :=
  ((D.cnew ^ clock 0 t : ℝ) : ℂ) * z + (clock 1 t : ℂ) * D.bpt y +
    (D.cnew : ℂ) * (D.Msig y (clock 2 t) z - z) +
    (D.cnew : ℂ) * (D.qin y (clock 3 t) z - D.bpt y - D.A0 y z) +
    ((D.cnew ^ (1 - clock 4 t) - D.cnew : ℝ) : ℂ) * (D.qin y 1 z - D.bpt y)

/-- `γ_t = c^{2S(5t) - 2S(5t-4)}`. -/
def gammaDet (t : ℝ) : ℝ := D.cnew ^ (2 * clock 0 t - 2 * clock 4 t)

/-- The path data (`h = 1`, source-order parameter `e_q = 2η`). -/
def pathData (y : Moments m) : Qhat.PathData where
  path := D.ordPath y
  gam := D.gammaDet
  h := 1
  e := 2 * D.eta
  pdag := D.pdag
  Psupp := D.Psupp
  c := D.cnew

/-! ### §7 the Hamiltonian -/

/-- The planar Hamiltonian `Q_y` of the whole-path normalised isotopy (generic `Qhat.Qham`:
area normalisation, flow, source primitive; convention `ι_X ω = -dQ`), in real coordinates. -/
def rawGen (y : Moments m) (s : ℝ) (w : ℝ × ℝ) : ℝ := Qhat.Qham (D.pathData y) s ⟨w.1, w.2⟩

/-- **The planar generator** `B(y, s, w) = ψ(y) Q_y(ψ(y) s, w)`. -/
def gen (y : Moments m) (s : ℝ) (w : ℝ × ℝ) : ℝ :=
  D.cutoff y * D.rawGen y (D.cutoff y * s) w

/-! ### Elementary facts -/

variable {D}

theorem gen_of_cutoff_eq_zero {y : Moments m} (h : D.cutoff y = 0) (s : ℝ) (w : ℝ × ℝ) :
    D.gen y s w = 0 := by
  simp [gen, h]

theorem eta_pos (hξ : 0 < D.xi) (hL : 0 ≤ D.L) : 0 < D.eta := by
  unfold eta
  have : 0 < D.xi / (32 * (D.L + 1)) := div_pos hξ (by linarith)
  have := lt_min (by norm_num : (0 : ℝ) < 1 / 16) this
  linarith

theorem eta_le : D.eta ≤ 1 / 32 := by
  unfold eta
  have := min_le_left (1 / 16 : ℝ) (D.xi / (32 * (D.L + 1)))
  linarith

theorem sig_pos (hξ : 0 < D.xi) : 0 < D.sig := div_pos hξ (by norm_num)

theorem kappa_pos (hξ : 0 < D.xi) (hL : 0 ≤ D.L) : 0 < D.kappa :=
  div_pos (mul_pos (sig_pos hξ) (eta_pos hξ hL)) (by norm_num)

theorem tol_pos (hξ : 0 < D.xi) : 0 < D.tol := div_pos hξ (by norm_num)

theorem clse_pos (hξ : 0 < D.xi) : 0 < D.clse :=
  div_pos (by positivity) (sig_pos hξ)

theorem beta_pos (hξ : 0 < D.xi) (hL : 0 ≤ D.L) : 0 < D.beta :=
  div_pos (eta_pos hξ hL) (by norm_num)

theorem beta_lt_one : D.beta < 1 := by
  unfold beta; linarith [D.eta_le]

theorem nu_pos (hξ : 0 < D.xi) (hL : 0 ≤ D.L) : 0 < D.nu := by
  unfold nu
  have h1 := sig_pos hξ; have h2 := beta_pos hξ hL
  have h3 : 0 < 1 - D.beta := by linarith [D.beta_lt_one]
  exact mul_pos (mul_pos (mul_pos (by norm_num) h1) h2) h3

theorem r0_pos (hξ : 0 < D.xi) (hL : 0 ≤ D.L) : 0 < D.r0 := by
  have hk := kappa_pos hξ hL
  exact lt_min (by norm_num) (Real.sqrt_pos.2 (div_pos hk (by linarith)))

theorem r0_le : D.r0 ≤ 1 / 8 := min_le_left _ _

theorem pdag_pos (hξ : 0 < D.xi) (hL : 0 ≤ D.L) : 0 < D.pdag := by
  unfold pdag; linarith [D.eta_le]

theorem pdag_lt_one (hξ : 0 < D.xi) (hL : 0 ≤ D.L) : D.pdag < 1 := by
  unfold pdag; linarith [eta_pos hξ hL]

/-- Source order of the path data: `p₊ = 1 - 15 e_q/4 < p†` and `4 e_q < 1`. -/
theorem pathData_order (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (y : Moments m) :
    0 < (D.pathData y).e ∧ 4 * (D.pathData y).e < (D.pathData y).h ∧
      (D.pathData y).h - 15 * (D.pathData y).e / 4 < (D.pathData y).pdag := by
  have := eta_pos hξ hL
  have := D.eta_le
  refine ⟨?_, ?_, ?_⟩ <;> simp only [pathData, pdag] <;> linarith

theorem rbmax_lt_Rh (hξ : 0 < D.xi) (hL : 0 ≤ D.L) : D.rbmax < Rh := by
  have := r0_pos hξ hL
  have := D.r0_le
  exact Real.sqrt_lt_sqrt (div_nonneg (by linarith) Real.pi_pos.le)
    (div_lt_div_of_pos_right (by linarith) Real.pi_pos)

end Input

/-! ### The input for a normalised slice family of a polytope -/

/-- Uniform bound `Σ_{ν : b_{νj} > 0} (|ℓ_ν| + 4R Σ_i |b_{νi}|)/b_{νj} + 1` for the inner slice
length on the box `‖y‖_∞ < 4R`. -/
def lenBound (Δ : Polytope m q) (j : Fin m) (R : ℝ) : ℝ :=
  (∑ ν, if 0 < Δ.b ν j then (|Δ.ℓ ν| + 4 * R * ∑ i, |Δ.b ν i|) / Δ.b ν j else 0) + 1

/-- The parameter cutoff `ψ(y) = Π_i S((16R² - y_i²)/(7R²)) · Π_{ν : b_{νj}>0} S((L_ν(y) - η₀/2)/(η₀/4))`:
one on `{‖y‖_∞ ≤ 3R, all L_ν ≥ 3η₀/4}` and zero off `{‖y‖_∞ < 4R, all L_ν > η₀/2}`. -/
def paramCut (Δ : Polytope m q) (j : Fin m) (Lν : Fin q → Moments m → ℝ) (R η₀ : ℝ)
    (y : Moments m) : ℝ :=
  (∏ i, Real.smoothTransition ((16 * R ^ 2 - y i ^ 2) / (7 * R ^ 2))) *
    ∏ ν, (if 0 < Δ.b ν j then Real.smoothTransition ((Lν ν y - η₀ / 2) / (η₀ / 4)) else 1)

/-- The input for the slice family `f_y(v) = F(y, ℓ(y) v)` (pieces `a(y|_{j=0}) + a_j ℓ(y) v`),
face lengths `Lν`, box radius `R`, length scale `η₀` and tolerance `ξ`. -/
def sliceInput (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (ell : Moments m → ℝ)
    (Lν : Fin q → Moments m → ℝ) (R η₀ ξ : ℝ) : Input m where
  pieces y := F.map fun a => (a.eval (Function.update y j 0), a.coef j * ell y)
  n := F.length
  xi := ξ
  L := (F.map fun a => |a.coef j|).sum * lenBound Δ j R + 1
  M := (F.map fun a => |a.const| + 4 * R * (∑ i, |a.coef i|) + |a.coef j| * lenBound Δ j R).sum + 1
  cutoff := paramCut Δ j Lν R η₀

theorem sliceInput_L_nonneg (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (ell : Moments m → ℝ)
    (Lν : Fin q → Moments m → ℝ) {R : ℝ} (hR : 0 ≤ R) (η₀ ξ : ℝ) :
    0 ≤ (sliceInput Δ F j ell Lν R η₀ ξ).L := by
  have h1 : 0 ≤ (F.map fun a => |a.coef j|).sum :=
    List.sum_nonneg (by intro x hx; obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)
  have h2 : 0 ≤ lenBound Δ j R := by
    unfold lenBound
    have : 0 ≤ ∑ ν, (if 0 < Δ.b ν j then (|Δ.ℓ ν| + 4 * R * ∑ i, |Δ.b ν i|) / Δ.b ν j else 0) :=
      Finset.sum_nonneg fun ν _ => by
        split_ifs with h
        · exact div_nonneg (add_nonneg (abs_nonneg _)
            (mul_nonneg (by linarith) (Finset.sum_nonneg fun i _ => abs_nonneg _))) h.le
        · exact le_rfl
    linarith
  show 0 ≤ (F.map fun a => |a.coef j|).sum * lenBound Δ j R + 1
  have := mul_nonneg h1 h2
  linarith

end SymplecticPacking.HighDim.PlanarGen
