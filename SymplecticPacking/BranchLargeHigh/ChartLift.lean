import SymplecticPacking.BranchLargeHigh.Phase
import SymplecticPacking.BranchSmall.Transfer
import SymplecticPacking.BranchSmall.ZeroSection
import SymplecticPacking.BranchLargeHigh.LiftPrimitive

/-!
# The chart lift `(φ, Ĵ)` of the second stage (supplement `lem:two-identification`)

Dimension `m = q + 3`, curve `Γ = locus (parameters q)`
in the affine chart `Affine (q + 2) = ℂ^{q+3}` of `CP^{q+3}`, ball chart
`affineRadialTarget (q + 2) (1/π)` onto `B°(1) ⊂ ℂ^{q+3}`.

* `φ = vectorTransfer q h₂ b₂` is the explicit vector normal transfer of `E₂ = O_Γ(2)^{⊕(q+2)}`
  (`BranchSmall.vectorTransfer`), at the transfer height `b₂ = (2h₂ + 1)/4 ∈ (h₂, 1/2)`.
* Over the ball chart, `O(1)` has the unitary frame with angular connection
  `α = dθ − λ_base`, `λ_base(ξ)(v) = ½ Σ Im(conj ξ_i v_i)` (`Coupled.lean`, `θ` in turns). Parallel
  transport along a base path `ξ(τ)` multiplies the fibre coordinate by
  `exp(2πi ∫ λ_base(ξ)(ξ̇) dτ)` (`lineAction`).
* `J` is parallel transport along the base homotopy `φ_τ` of §2 (graph transport, then the inverse
  Moser return). With `f(b,w) = ∫₀¹ ξ_{(b,tw)}(0,w) dt`, `ξ = J^*α − (α_C − λ)`, one has
  (radial Stokes, `λ(0,w) = 0` along the radial ray, `pr_*(0,w) = 0`)

    `Θ(b,w) − f(b,w) = Θ(b,0) + ∫₀¹ λ_base(φ(b,tw))(∂_t φ(b,tw)) dt`,

  where `Θ(b,w)` is the transport phase of `J`. Hence `Ĵ = J ∘ e^{−2πif}` is multiplication by
  `exp(2πi Ψ(b,w))`, `Ψ = zeroPhase + radialPhase` (`liftPhase`). Only the homotopy of the zero
  section (`zeroPath`, `returnPath`) and `φ` itself enter.

The O(1) fibre coordinate `z₀` of the mixed model is the coordinate in the same unitary frame at the
curve point `chart(b)` (the frame of `CP^{q+3} ∖ F` restricted to the affine curve).
-/

noncomputable section

namespace SymplecticPacking.BranchLargeHigh.Two

open Set MeasureTheory Problem
open SymplecticPacking.HighDim
open OAI.PackingSufficiencySupport (Ambient)
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit

/-- The action `∫₀¹ λ_base(γ(t))(γ'(t)) dt` of a base path; the phase (in turns) of unitary
parallel transport of `O(1)` along `γ` in the ball-chart frame. -/
def lineAction {n : ℕ} (γ : ℝ → Ambient n) : ℝ :=
  ∫ t in (0 : ℝ)..1, lamAmb (γ t) (deriv γ t)

/-- The ball chart `CP^{q+3} ∖ F ≅ B°(1)` on the affine chart of the curve. -/
def ballChart (q : ℕ) (z : Affine (q + 2)) : Ambient (q + 3) :=
  affineRadialTarget (q + 2) (1 / Real.pi) z

/-- The transfer height `b₂ = (2h₂ + 1)/4`, strictly between `h₂` and `1/2` when `h₂ < 1/2`. -/
def transferHeight (h₂ : ℝ) : ℝ := (2 * h₂ + 1) / 4

/-- The fibre coordinates `w ∈ ℂ^{q+2}` of `E₂` inside the mixed fibre `ℂ^{q+3}`. -/
def tailFibre {q : ℕ} (ζ : Fibre (q + 3)) : Fibre (q + 2) := fun j => ζ j.succ

/-- The second-stage base map `φ = 𝒯_{h₂,b₂}` (vector normal transfer into the ball chart). -/
def basePhi (q : ℕ) (h₂ : ℝ) (b : Surface q) (w : Fibre (q + 2)) : Ambient (q + 3) :=
  BranchSmall.vectorTransfer q h₂ (transferHeight h₂) (b, w)

/-- First half of the base homotopy over the zero section: the base projection of the graph
transport `T ↦ π_D τ_T ι_b(b, 0)`, read in the ball chart. -/
def zeroPath (q : ℕ) (h₂ : ℝ) (b : Surface q) (T : ℝ) : Ambient (q + 3) :=
  ballChart q (BranchSmall.VT.flowI
    (BranchSmall.VT.transportField (parameters q) (transferHeight h₂)) 0
    (BranchSmall.VT.radialInj (transferHeight h₂) b.val 0) T).1

/-- Second half: the inverse graph-to-FS Moser return of the transport endpoint, run from
`s = 1` to `s = 0` (`σ ↦ ψ_{1-σ}`), read in the ball chart. Its endpoint is `φ(b, 0)`. -/
def returnPath (q : ℕ) (h₂ : ℝ) (b : Surface q) (σ : ℝ) : Ambient (q + 3) :=
  ballChart q (BranchSmall.VT.flowI
    (BranchSmall.VT.returnField (parameters q) (transferHeight h₂)) 1
    (BranchSmall.VT.transport (parameters q) (transferHeight h₂)
      (BranchSmall.VT.radialInj (transferHeight h₂) b.val 0)).1 (1 - σ))

/-- `Θ(b, 0)`: the parallel-transport phase of `J` over the zero section. -/
def zeroPhase (q : ℕ) (h₂ : ℝ) (b : Surface q) : ℝ :=
  lineAction (zeroPath q h₂ b) + lineAction (returnPath q h₂ b)

/-- `∫₀¹ λ_base(φ(b,tw))(∂_t φ(b,tw)) dt`: the radial part of `Θ − f`. -/
def radialPhase (q : ℕ) (h₂ : ℝ) (b : Surface q) (w : Fibre (q + 2)) : ℝ :=
  lineAction (fun t : ℝ => basePhi q h₂ b (t • w))

/-- The total phase `Ψ = Θ − f` of `Ĵ = J ∘ e^{−2πif}` (in turns). -/
def liftPhase (q : ℕ) (h₂ : ℝ) (b : Surface q) (w : Fibre (q + 2)) : ℝ :=
  zeroPhase q h₂ b + radialPhase q h₂ b w

theorem zeroPath_eq_constant (q : ℕ) (h₂ : ℝ) (b : Surface q) :
    zeroPath q h₂ b = fun _ => ballChart q b.val := by
  funext T
  unfold zeroPath
  rw [BranchSmall.VT.radialInj_zero, BranchSmall.VT.flowI_stationary 0 T (b.val, 0)
    (fun s _ => BranchSmall.VT.transportField_zero_normal _ _ s _)]

theorem returnPath_eq_constant (q : ℕ) (h₂ : ℝ) (b : Surface q) :
    returnPath q h₂ b = fun _ => ballChart q b.val := by
  funext σ
  unfold returnPath
  rw [BranchSmall.VT.radialInj_zero, BranchSmall.VT.transport_zero_normal]
  rw [BranchSmall.VT.flowI_stationary 1 (1 - σ) b.val
    (fun s _ => BranchSmall.VT.returnField_zero_locus _ _ s _ b.property)]

theorem lineAction_constant {n : ℕ} (ξ : Ambient n) : lineAction (fun _ => ξ) = 0 := by
  simp [lineAction, lamAmb]

/-- The homotopy fixes the curve, so its zero-section transport phase vanishes. -/
theorem zeroPhase_eq_zero (q : ℕ) (h₂ : ℝ) (b : Surface q) : zeroPhase q h₂ b = 0 := by
  simp only [zeroPhase, zeroPath_eq_constant, returnPath_eq_constant, lineAction_constant, add_zero]

/-- The normal transfer agrees with the ball chart on the zero section. -/
theorem basePhi_zero (q : ℕ) (h₂ : ℝ) (b : Surface q) :
    basePhi q h₂ b 0 = ballChart q b.val := by
  unfold basePhi BranchSmall.vectorTransfer BranchSmall.VT.transferMap
  rw [BranchSmall.VT.toC_zero, BranchSmall.VT.radialInj_zero,
    BranchSmall.VT.transport_zero_normal, BranchSmall.VT.returnInv_zero_locus _ _ _ b.property]
  rfl

/-- A plane point as a complex number. -/
def planeC (p : ℝ × ℝ) : ℂ := ⟨p.1, p.2⟩

/-- **The chart lift** `(φ, Ĵ)` on unmixed coordinates `(b, (z₀, w))`: the base coordinate is
`ξ = φ(b, w)`, the first-normal fibre coordinate is `exp(2πiΨ(b,w)) · z₀`, assembled as the point
`(fibre, ξ)` of the coupled model `E (q + 4)` (`zc · 0` = fibre, `zc · i.succ` = base). The
parameter `h₁` (the `O(1)` height) does not enter the formula; it bounds `u` on the images. -/
def chartLiftExplicit (q : ℕ) (_h₁ h₂ : ℝ) (x : Surface q × Fibre (q + 3)) : E (q + 4) :=
  ofPhase (Fin.cons
    (Complex.exp (2 * Real.pi * Complex.I * (liftPhase q h₂ x.1 (tailFibre x.2) : ℂ)) *
      planeC (x.2 0))
    (basePhi q h₂ x.1 (tailFibre x.2)))

/-- The lift does not change the fibre moment `u = π|z₀|²`. -/
theorem fibMoment_chartLiftExplicit (q : ℕ) (h₁ h₂ : ℝ) (x : Surface q × Fibre (q + 3)) :
    fibMoment (chartLiftExplicit q h₁ h₂ x) = Real.pi * ((x.2 0).1 ^ 2 + (x.2 0).2 ^ 2) := by
  have he : Complex.normSq
      (Complex.exp (2 * Real.pi * Complex.I * (liftPhase q h₂ x.1 (tailFibre x.2) : ℂ))) = 1 := by
    have : 2 * Real.pi * Complex.I * (liftPhase q h₂ x.1 (tailFibre x.2) : ℂ) =
        ((2 * Real.pi * liftPhase q h₂ x.1 (tailFibre x.2) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [this, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]
  simp only [fibMoment, chartLiftExplicit, zc_ofPhase, Fin.cons_zero, map_mul, he, one_mul,
    planeC, Complex.normSq_mk]
  ring

/-- The base coordinate of the lift is `φ(b, w)`. -/
theorem zc_succ_chartLiftExplicit (q : ℕ) (h₁ h₂ : ℝ) (x : Surface q × Fibre (q + 3))
    (i : Fin (q + 3)) :
    zc (chartLiftExplicit q h₁ h₂ x) i.succ = basePhi q h₂ x.1 (tailFibre x.2) i := by
  simp [chartLiftExplicit]

end SymplecticPacking.BranchLargeHigh.Two
