import SymplecticPacking.HighDim.Handle.RawManifoldNaturality
import SymplecticPacking.HighDim.Handle.RawManifoldFamily

/-!
# Exterior derivatives of native ambient primitives

Euclidean exterior differentiation of native ambient primitives, with semantic naturality.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
variable {E P : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def ambientFamilyExterior (Γ : P → E → E →L[ℝ] ℝ) (p : P) (z : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  euclideanExteriorOneForm (Γ p) z

theorem joint_covector_fderiv_slice {Γ : P × E → E →L[ℝ] ℝ} {q : P × E}
    (hΓ : DifferentiableAt ℝ Γ q) :
    fderiv ℝ (fun y => Γ (q.1,y)) q.2=
      (fderiv ℝ Γ q).comp ((0 : E →L[ℝ] P).prod (ContinuousLinearMap.id ℝ E)) := by
  have hi : HasFDerivAt (fun y : E => (q.1,y))
      ((0 : E →L[ℝ] P).prod (ContinuousLinearMap.id ℝ E)) q.2 :=
    (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
  exact (hΓ.hasFDerivAt.comp q.2 hi).fderiv

theorem ambientFamilyExterior_contDiff {Γ : P → E → E →L[ℝ] ℝ}
    (hΓ : ContDiff ℝ ∞ (fun q : P × E => Γ q.1 q.2)) :
    ContDiff ℝ ∞ (fun q : P × E => ambientFamilyExterior Γ q.1 q.2) := by
  let J := (0 : E →L[ℝ] P).prod (ContinuousLinearMap.id ℝ E)
  have hD : ContDiff ℝ ∞ (fun q : P × E => (fderiv ℝ (fun q : P × E => Γ q.1 q.2) q).comp J) :=
    (hΓ.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const
  apply contDiff_clm_apply_iff.mpr
  intro u
  apply contDiff_clm_apply_iff.mpr
  intro v
  have h1 := (hD.clm_apply (contDiff_const (c := u))).clm_apply (contDiff_const (c := v))
  have h2 := (hD.clm_apply (contDiff_const (c := v))).clm_apply (contDiff_const (c := u))
  have heq : (fun q : P × E => ambientFamilyExterior Γ q.1 q.2 u v)=
      fun q => ((fderiv ℝ (fun q : P × E => Γ q.1 q.2) q).comp J) u v-
        ((fderiv ℝ (fun q : P × E => Γ q.1 q.2) q).comp J) v u := by
    funext q
    unfold ambientFamilyExterior euclideanExteriorOneForm
    rw [joint_covector_fderiv_slice (hΓ.differentiable (by simp) q)]
    rfl
  rw [heq]
  exact h1.sub h2

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem semantic_ambient_exterior {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι)
    {Γ : E → E →L[ℝ] ℝ} (hΓ : ContDiff ℝ ∞ Γ) :
    manifoldExteriorOneForm (semanticOneForm ι (fun x => Γ (ι x)))=
      semanticTwoForm ι (fun x => euclideanExteriorOneForm Γ (ι x)) := by
  funext x
  have hc : ContDiffAt ℝ ∞ (chartOneForm Γ (ι x))
      (extChartAt 𝓘(ℝ,E) (ι x) (ι x)) := by
    rw [show chartOneForm Γ (ι x)=Γ from funext (vector_chartOneForm Γ (ι x))]
    simpa only [mfld_simps] using hΓ.contDiffAt (x := ι x)
  have hd := manifold_pullback_exterior_at (E := E) (F := Plane) (M := E) (N := M)
    (g := ι) hc (hι.contMDiffAt (x := x))
  have hp : manifoldPullbackOneForm (E := E) (F := Plane) (fun _ : ℝ => Γ) ι 0=
      semanticOneForm ι (fun x => Γ (ι x)) := by
    funext y
    apply ContinuousLinearMap.ext
    intro u
    rfl
  rw [hp,vector_exteriorOneForm] at hd
  exact hd

theorem ambientFamilyExterior_restriction_smooth {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι)
    {Γ : P → E → E →L[ℝ] ℝ}
    (hΓ : ContDiff ℝ ∞ (fun q : P × E => Γ q.1 q.2)) :
    ContMDiff ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun q : P × M => ambientFamilyExterior Γ q.1 (ι q.2)) :=
  (ambientFamilyExterior_contDiff hΓ).contMDiff.comp
    (contMDiff_fst.prodMk_space (hι.comp contMDiff_snd))

theorem ambient_primitive_restriction {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι)
    {Γ : E → E →L[ℝ] ℝ} (hΓ : ContDiff ℝ ∞ Γ) :
    RawIsPrimitive ι (fun x => euclideanExteriorOneForm Γ (ι x)) (fun x => Γ (ι x)) := by
  apply rawIsPrimitive_of_semantic hι (hΓ.contMDiff.comp hι)
  · intro x u v
    change fderiv ℝ Γ (ι x) u v-fderiv ℝ Γ (ι x) v u =
      -(fderiv ℝ Γ (ι x) v u-fderiv ℝ Γ (ι x) u v)
    ring
  · exact semantic_ambient_exterior hι hΓ

#check_explicit ambientFamilyExterior
end SymplecticPacking.HighDim.ToricPackingStages
