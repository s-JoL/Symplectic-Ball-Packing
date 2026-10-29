import SymplecticPacking.BranchSmall.TransferPotentials
import SymplecticPacking.BranchSmall.RadialInjectionForm
import SymplecticPacking.BranchSmall.ReturnMoser
import SymplecticPacking.BranchSmall.TransportMoser
import SymplecticPacking.Forms.Basic
import SymplecticPacking.HighDim.Comparator.Isotopy
import OAI.Geometry.BallPacking.Models.RationalSlack

/-!
# The symplectic identity of the vector transfer (supplement thm:vtr-transfer (a),(c))

Supporting lemmas for `transferMap_form` (`VectorTransferStages.lean`). With
`R x = ι_b(x)`, `τ = transport`, `ψ₁⁻¹ = returnInv` and the ball chart `C = affineRadialTarget`,

  `transferMap = C ∘ ψ₁⁻¹ ∘ pr ∘ τ ∘ R`,

and the identity `𝒯^* ω₀ = Ω_N` is the chain

* `chart_form`: `C^* ω₀ = ω_FS = dd^c log(1 + |z|²) = ω_0` (proved);
* `returnInv_form`: `(ψ₁⁻¹)^* ω_0 = ω_1` (Moser, prop:vtr-return);
* `graph_form`: on the graph `X₁ = {W = F(z)}`, `Ω_b = pr^* ω_1` (proved: the graph map is
  holomorphic and `bundlePot ∘ graph = returnPot 1`);
* `transport_form`: `τ^* (Ω_b|X₁) = Ω_b|X₀`, and `τ` maps `T X₀` to `T X₁` (prop:vtr-transport);
* `radial_tangent`: `R` takes values in `X₀ = locus × ℂ^q` (proved);
* `radial_form`: `R^* Ω_b = Ω_N` (lem:vtr-injection).

`transferMap_form_of` assembles them by the chain rule (proved).
-/

noncomputable section

namespace SymplecticPacking.BranchSmall

open Set Manifold
open SymplecticPacking.HighDim
open OAI.PackingSufficiencySupport (Ambient openBall)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold



/-! ### The radial stage -/

/-- The radial injection on the model, `R x = ι_b(x)`. -/
def radialStage (m : ℕ) (b : ℝ) (x : Surface m × Fibre (m + 2)) : VT.Tot (m + 2) :=
  VT.radialInj b x.1.val (VT.toC x.2)

/-- `R` takes values in `X₀ = locus × ℂ^q`, so its differential is tangent to `X₀`. -/
theorem radial_tangent (m : ℕ) (b : ℝ) (x : Surface m × Fibre (m + 2))
    (hR : MDifferentiableAt 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, VT.Tot (m + 2))
      (radialStage m b) x)
    (v : (ℝ × ℝ) × Fibre (m + 2)) :
    jacobian (radialStage m b x).1
      (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, VT.Tot (m + 2)) (radialStage m b) x v).1
      = 0 := by
  let E : VT.Tot (m + 2) → (Fin (m + 2) → ℂ) := fun y => equations (parameters m) y.1
  have hE : HasFDerivAt E
      (((jacobian (radialStage m b x).1).restrictScalars ℝ).comp
        (ContinuousLinearMap.fst ℝ (Affine (m + 2)) (Fin (m + 2) → ℂ))) (radialStage m b x) :=
    ((equations_hasFDerivAt (parameters m) _).restrictScalars ℝ).comp _ hasFDerivAt_fst
  have hc := mfderiv_comp x hE.differentiableAt.mdifferentiableAt hR
  have hz : E ∘ radialStage m b = fun _ => 0 := by
    funext x
    exact x.1.property
  rw [hz, mfderiv_const, mfderiv_eq_fderiv, hE.fderiv] at hc
  have := congrArg (fun L => L v) hc
  exact this.symm

/-- **Radial injection** (lem:vtr-injection): `ι_b^* Ω_b = Ω_N` on the tube `{|p| < b}`. -/
theorem radial_form (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (x : Surface m × Fibre (m + 2)) (hx : ∑ j, planeMoments x.2 j < b)
    (v w : (ℝ × ℝ) × Fibre (m + 2)) :
    VT.bundleForm b (radialStage m b x)
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, VT.Tot (m + 2)) (radialStage m b) x v)
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, VT.Tot (m + 2)) (radialStage m b) x w)
      = globalHorizontalCoupling phaseArea
          (normalHorizontalPrimitive (parameters m) 2 ∘ planeMoments) x v w := by
  have hsum : (∑ j, planeMoments x.2 j) = Real.pi * phaseSq x.2 := by
    simp only [planeMoments, radialArea, radiusSq, phaseSq, phaseDot_apply, pow_two, ← Finset.mul_sum]
  have hx' : phaseSq x.2 < b / Real.pi := (lt_div_iff₀ Real.pi_pos).mpr (by nlinarith [hsum])
  exact VT.radialCurveMap_form (parameters m) hb0 x hx' v w

/-! ### Transport and Moser return -/

/-- **Transport** (prop:vtr-transport (d),(e)): the time-one horizontal transport maps tangent
vectors of `X₀ = {F = 0}` at `ι_b(x)` to tangent vectors of `X₁ = {F = W}` and preserves `Ω_b`
on them. -/
theorem transport_form (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (x : Affine (m + 2) × PlanePhase (Fin (m + 2))) (hx1 : x.1 ∈ locus (parameters m))
    (hx2 : Real.pi * VT.wsq (VT.toC x.2) < b) (u u' : VT.Tot (m + 2))
    (hu : jacobian (VT.radialInj b x.1 (VT.toC x.2)).1 u.1 = 0)
    (hu' : jacobian (VT.radialInj b x.1 (VT.toC x.2)).1 u'.1 = 0) :
    (fderiv ℝ (VT.transport (parameters m) b) (VT.radialInj b x.1 (VT.toC x.2)) u).2 =
        jacobian (VT.transport (parameters m) b (VT.radialInj b x.1 (VT.toC x.2))).1
          (fderiv ℝ (VT.transport (parameters m) b) (VT.radialInj b x.1 (VT.toC x.2)) u).1 ∧
      VT.bundleForm b (VT.transport (parameters m) b (VT.radialInj b x.1 (VT.toC x.2)))
          (fderiv ℝ (VT.transport (parameters m) b) (VT.radialInj b x.1 (VT.toC x.2)) u)
          (fderiv ℝ (VT.transport (parameters m) b) (VT.radialInj b x.1 (VT.toC x.2)) u')
        = VT.bundleForm b (VT.radialInj b x.1 (VT.toC x.2)) u u' := by
  exact VT.transport_form_all m hb0 hb x hx1 hx2 u u' hu hu'

/-- **Moser return** (prop:vtr-return (c)): `(ψ₁⁻¹)^* ω_0 = ω_1` at the projected transport
image of the tube. -/
theorem returnInv_form (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (x : Affine (m + 2) × PlanePhase (Fin (m + 2))) (hx1 : x.1 ∈ locus (parameters m))
    (hx2 : Real.pi * VT.wsq (VT.toC x.2) < b) (v w : Affine (m + 2)) :
    VT.ddcForm (VT.returnPot (parameters m) b 0)
        (VT.returnInv (parameters m) b
          (VT.transport (parameters m) b (VT.radialInj b x.1 (VT.toC x.2))).1)
        (fderiv ℝ (VT.returnInv (parameters m) b)
          (VT.transport (parameters m) b (VT.radialInj b x.1 (VT.toC x.2))).1 v)
        (fderiv ℝ (VT.returnInv (parameters m) b)
          (VT.transport (parameters m) b (VT.radialInj b x.1 (VT.toC x.2))).1 w)
      = VT.ddcForm (VT.returnPot (parameters m) b 1)
          (VT.transport (parameters m) b (VT.radialInj b x.1 (VT.toC x.2))).1 v w := by
  exact VT.returnInv_form_all m hb0 hb _ v w

/-! ### Assembly -/

/-- **thm:vtr-transfer (a),(c)** from the stage identities, by the chain rule. -/
theorem transferMap_form_of (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (x : Surface m × Fibre (m + 2)) (hx : ∑ j, planeMoments x.2 j < b)
    (hR : MDifferentiableAt 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, VT.Tot (m + 2))
      (radialStage m b) x)
    (hT : DifferentiableAt ℝ (VT.transport (parameters m) b) (radialStage m b x))
    (hP : DifferentiableAt ℝ (VT.returnInv (parameters m) b)
      (VT.transport (parameters m) b (radialStage m b x)).1)
    (hgraph : (VT.transport (parameters m) b (radialStage m b x)).2 =
      equations (parameters m) (VT.transport (parameters m) b (radialStage m b x)).1)
    (v w : (ℝ × ℝ) × Fibre (m + 2)) :
    successorStandardForm (m + 2)
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, Ambient (m + 3))
          (fun x : Surface m × Fibre (m + 2) => VT.transferMap (parameters m) b (x.1.val, x.2)) x v)
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, Ambient (m + 3))
          (fun x : Surface m × Fibre (m + 2) => VT.transferMap (parameters m) b (x.1.val, x.2)) x w)
      = globalHorizontalCoupling phaseArea
          (normalHorizontalPrimitive (parameters m) 2 ∘ planeMoments) x v w := by
  have hC : DifferentiableAt ℝ (affineRadialTarget (m + 2) (1 / Real.pi))
      (VT.returnInv (parameters m) b (VT.transport (parameters m) b (radialStage m b x)).1) :=
    (affineRadialTarget_smooth (m + 2) (1 / Real.pi)).differentiable (by simp) _
  have hG := hC.hasFDerivAt.comp (radialStage m b x)
    (hP.hasFDerivAt.comp (radialStage m b x)
      ((hasFDerivAt_fst (p := VT.transport (parameters m) b (radialStage m b x))).comp
        (radialStage m b x) hT.hasFDerivAt))
  have hF : (fun x : Surface m × Fibre (m + 2) => VT.transferMap (parameters m) b (x.1.val, x.2)) =
      (affineRadialTarget (m + 2) (1 / Real.pi) ∘ (VT.returnInv (parameters m) b ∘
        (Prod.fst ∘ VT.transport (parameters m) b))) ∘ radialStage m b := rfl
  have hD : ∀ u, mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, Ambient (m + 3))
      (fun x : Surface m × Fibre (m + 2) => VT.transferMap (parameters m) b (x.1.val, x.2)) x u =
      fderiv ℝ (affineRadialTarget (m + 2) (1 / Real.pi))
        (VT.returnInv (parameters m) b (VT.transport (parameters m) b (radialStage m b x)).1)
        (fderiv ℝ (VT.returnInv (parameters m) b)
          (VT.transport (parameters m) b (radialStage m b x)).1
          (fderiv ℝ (VT.transport (parameters m) b) (radialStage m b x)
            (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, VT.Tot (m + 2))
              (radialStage m b) x u)).1) := by
    intro u
    rw [hF, mfderiv_comp x hG.differentiableAt.mdifferentiableAt hR, mfderiv_eq_fderiv,
      hG.fderiv]
    rfl
  rw [show (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, Ambient (m + 3))
      (fun x : Surface m × Fibre (m + 2) => VT.transferMap (parameters m) b (x.1.val, x.2)) x v)
      = _ from hD v,
    show (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, Ambient (m + 3))
      (fun x : Surface m × Fibre (m + 2) => VT.transferMap (parameters m) b (x.1.val, x.2)) x w)
      = _ from hD w]
  have hx1 : x.1.val ∈ locus (parameters m) := x.1.property
  have hx2 : Real.pi * VT.wsq (VT.toC x.2) < b := by
    have he : (∑ j, planeMoments x.2 j) = Real.pi * VT.wsq (VT.toC x.2) := by
      rw [VT.pi_wsq_toC]; rfl
    rw [← he]; exact hx
  have htv := radial_tangent m b x hR v
  have htw := radial_tangent m b x hR w
  obtain ⟨hTv, hform⟩ := transport_form m hb0 hb (x.1.val, x.2) hx1 hx2 _ _ htv htw
  obtain ⟨hTw, -⟩ := transport_form m hb0 hb (x.1.val, x.2) hx1 hx2 _ _ htw htv
  have hr : radialStage m b x = VT.radialInj b (x.1.val, x.2).1 (VT.toC (x.1.val, x.2).2) := rfl
  rw [hr] at hgraph
  rw [hr]
  rw [VT.chart_form (parameters m) b, returnInv_form m hb0 hb (x.1.val, x.2) hx1 hx2]
  exact ((VT.graph_form (parameters m) b hgraph hTv hTw).symm.trans hform).trans
    (radial_form m hb0 hb x hx v w)

end SymplecticPacking.BranchSmall
