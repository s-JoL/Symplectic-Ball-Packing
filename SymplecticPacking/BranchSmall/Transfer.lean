import SymplecticPacking.BranchSmall.Model
import SymplecticPacking.BranchSmall.VectorTransferSpec
import SymplecticPacking.HighDim.Assembly
import SymplecticPacking.BranchSmall.VectorTransfer
import SymplecticPacking.BranchSmall.VectorTransferStages

/-!
# The vector normal transfer (paper thm:qdr-transfer; supplement S-thm:vtr-transfer)

For `0 < h < b < 1/2` the composition of
* the radial injection `W_j = √π U_j / √(b − |p|)` into the weight-two bundle,
* the horizontal transport along `F(Z) = T W` (`T : 0 → 1`) with the Hermitian metric matrices
  `A = 1 − 2b‖W‖²/(1+‖W‖²)`, `B = b[(1+‖W‖²)I − WW*]/(1+‖W‖²)²`, `S = A⁻¹JJ* + T²B⁻¹`,
  `Ż = A⁻¹J*S⁻¹W`, `Ẇ = −T B⁻¹ S⁻¹ W`,
* the inverse of the graph-to-FS Moser return (matrix `M_s ≥ (1 − 2b) I`),
* the ball chart `CP^n ∖ {Z_0 = 0} ≅ B°(1)`,
is a smooth symplectic embedding of the tube `{|p| < b}` over the affine curve into the open
unit-capacity ball. Every step is a formula or the flow of an explicit compactly supported
field (`Return.flow`). Compare the OpenAI library
`exists_actual_normal_transfer`, `exists_polynomial_target_embedding` (existence versions).
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

/-- The model form on `Surface m × ℂ^{m+2}`. -/
def quadricForm (m : ℕ) :
    ManifoldTwoForm ((ℝ × ℝ) × Fibre (m + 2)) (Surface m × Fibre (m + 2)) :=
  globalHorizontalCoupling phaseArea (normalHorizontalPrimitive (parameters m) 2 ∘ planeMoments)

/-- The tube `{|p| < b}`. -/
def transferDomain (m : ℕ) (b : ℝ) : Set (Surface m × Fibre (m + 2)) :=
  {x | ∑ j, planeMoments x.2 j < b}

theorem transferDomain_isOpen (m : ℕ) (b : ℝ) : IsOpen (transferDomain m b) := by
  apply isOpen_lt _ continuous_const
  exact continuous_finsetSum _ fun j _ =>
    (continuous_apply j).comp (planeMoments_smooth.continuous.comp continuous_snd)

/-- **The explicit vector transfer** `𝒯_{h,b}` (`VT.transferMap`: ball chart ∘ inverse Moser
return ∘ projection ∘ horizontal transport ∘ radial injection; see `VectorTransfer.lean`).
It does not depend on `h`: the transport is defined on the whole tube `{|p| < b}`. -/
def vectorTransfer (m : ℕ) (_h b : ℝ) : Surface m × Fibre (m + 2) → Ambient (m + 3) :=
  fun x => VT.transferMap (parameters m) b (x.1.val, x.2)

/-- **thm:qdr-transfer.** -/
theorem vectorTransfer_spec (m : ℕ) {h b : ℝ} (hh : 0 < h) (hhb : h < b) (hb : b < 1 / 2) :
    ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, Ambient (m + 3)) ∞
        (vectorTransfer m h b) (transferDomain m b) ∧
      Topology.IsEmbedding (fun x : transferDomain m b => vectorTransfer m h b x.val) ∧
      (∀ x ∈ transferDomain m b, ∀ v w, successorStandardForm (m + 2)
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, Ambient (m + 3)) (vectorTransfer m h b) x v)
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, Ambient (m + 3)) (vectorTransfer m h b) x w)
          = quadricForm m x v w) ∧
      ∀ x ∈ transferDomain m b, vectorTransfer m h b x ∈ openBall (m + 3) 1 := by
  have hb0 : 0 < b := hh.trans hhb
  exact ⟨transferMap_surface_contMDiffOn m hb0 hb, transferMap_surface_isEmbedding m hb0 hb,
    fun x hx v w => transferMap_form m hb0 hb x hx v w,
    fun x _ => VT.transferMap_mem (parameters m) b _⟩

end SymplecticPacking.BranchSmall
