import SymplecticPacking.HighDim.Handle.NativeModelAgreement

/-!
# Analytic estimates for the native packing formula

Normalization, comparator-isotopy and surface-remainder estimates used by the native packing
formula, proved from the raw construction.
-/

noncomputable section
namespace SymplecticPacking.HighDim
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open OAI.PackingSufficiencySupport.MomentPolytope
open ToricPackingStages
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [T2Space M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  [NormalSpace M] [SigmaCompactSpace M] {m q k : ℕ}

namespace RawModelAgreement
variable {T : RawToricModel E M m q} {S : ToricModel M m q} (h : RawModelAgreement T S)
include h

theorem handleDensity_semantic : semanticTwoForm T.presentation.inclusion T.handleDensity=
    S.handle.density S.hb := by
  funext x
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change T.handle.radial T.hb x (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) T.presentation.inclusion x u)*
      T.handle.dual x (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) T.presentation.inclusion x v)-
      T.handle.dual x (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) T.presentation.inclusion x u)*
      T.handle.radial T.hb x (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) T.presentation.inclusion x v)=_
  change (semanticOneForm T.presentation.inclusion (T.handle.radial T.hb) x u)*
      (semanticOneForm T.presentation.inclusion T.handle.dual x v)-
      (semanticOneForm T.presentation.inclusion T.handle.dual x u)*
      (semanticOneForm T.presentation.inclusion (T.handle.radial T.hb) x v)=_
  rw [h.handle.radial_eq,h.handle.dual_eq,h.hb_eq]
  rfl

theorem normalization_annular_exterior {reserve : ℝ} {outer : Moments m → ℝ}
    (hN : RawNormalizationSpec T reserve outer) : ∀ p x,x∈S.handle.chart.target →
    manifoldExteriorOneForm (semanticOneForm T.presentation.inclusion (T.normalPrimitive reserve p)) x=
      T.backgroundCoefficient reserve • S.Λ x+T.handleMass reserve p • S.handle.density S.hb x := by
  intro p x hx
  have hh := hN.annular_exterior p x (h.handle.target_eq.symm ▸ hx)
  rw [h.reference_eq,h.handleDensity_semantic] at hh
  exact hh

/-- The annular normal form, including its explicit positive reference primitive. -/
theorem normalization_normal_form
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ T.presentation.inclusion)
    {reserve : ℝ} {outer : Moments m → ℝ} (hN : RawNormalizationSpec T reserve outer) :
    ∃ (γ : ManifoldOneForm Plane M) (W : Set M),IsOpen W ∧
      S.handle.chart '' AnnularHandleData.band S.hb ⊆ W ∧ W ⊆ S.handle.chart.target ∧
      (∀ x∈S.handle.chart.target,ContDiffAt ℝ ∞ (chartOneForm γ x)
        (extChartAt 𝓘(ℝ,Plane) x x)) ∧
      (∀ x∈S.handle.chart.target,manifoldExteriorOneForm γ x=T.backgroundCoefficient reserve • S.Λ x) ∧
      ∀ p x,x∈W → semanticOneForm T.presentation.inclusion (T.normalPrimitive reserve p) x=
        γ x+(intervalClock (-S.hb) S.hb (S.handle.chart.symm x).1*T.handleMass reserve p) • S.handle.dual x := by
  let γ : ManifoldOneForm Plane M :=
    T.backgroundCoefficient reserve • semanticOneForm T.presentation.inclusion T.referencePrimitive
  obtain ⟨W,hW,hBW,hWA,hform⟩ := hN.normal_region
  have hγs := semanticOneForm_smooth hι hN.reference_smooth
  have hγx (x : M) : ContDiffAt ℝ ∞
      (chartOneForm (semanticOneForm T.presentation.inclusion T.referencePrimitive) x)
      (extChartAt 𝓘(ℝ,Plane) x x) :=
    hγs.spatial_smooth (0:ℝ) x (mem_extChartAt_target x)
  refine ⟨γ,W,hW,?_,?_,?_,?_,?_⟩
  · simpa only [h.handle.forward_eq,h.hb_eq] using hBW
  · simpa only [h.handle.target_eq] using hWA
  · intro x hx
    change ContDiffAt ℝ ∞ (chartOneForm
      (T.backgroundCoefficient reserve • semanticOneForm T.presentation.inclusion T.referencePrimitive) x) _
    rw [show chartOneForm (T.backgroundCoefficient reserve •
        semanticOneForm T.presentation.inclusion T.referencePrimitive) x=
        (fun y => T.backgroundCoefficient reserve •
          chartOneForm (semanticOneForm T.presentation.inclusion T.referencePrimitive) x y) from
      funext (chartOneForm_smul _ _ x)]
    exact (contDiffAt_const (c := T.backgroundCoefficient reserve)).smul (hγx x)
  · intro x hx
    rw [show γ=T.backgroundCoefficient reserve •
      semanticOneForm T.presentation.inclusion T.referencePrimitive from rfl,
      manifoldExteriorOneForm_smul_at (T.backgroundCoefficient reserve) (hγx x),
      hN.reference_exterior,h.reference_eq]
  · intro p x hx
    simpa only [h.hb_eq,h.handle.inverse_eq,h.handle.dual_eq,γ,Pi.smul_apply] using hform p x hx
end RawModelAgreement

namespace ToricPackingStages

/-- A face collar gives invariance in both time directions along the isotopy. -/
theorem fibreIsotopy_region_iff {D : ComparisonDatum m} {Δ : Polytope m q}
    (hgen : GenSpec D.Q) (hcol : FaceCollar Δ D.Q) (t : ℝ) (ht : t∈Icc (0:ℝ) 1) (w : Fibre m) :
    (fibreIsotopy D).map t w∈planeRegion Δ.b Δ.ℓ ↔ w∈planeRegion Δ.b Δ.ℓ := by
  obtain ⟨η,hη,hzero⟩ := hcol
  let Φ := fibreIsotopy D
  have hμ (ν : Fin q) : ContDiff ℝ ∞ (fun v : Fibre m => ∑ j,Δ.b ν j*planeMoments v j) :=
    (momentFace_smooth (Δ.b ν)).comp planeMoments_smooth
  have he (ν : Fin q) : (∑ j,Δ.b ν j*planeMoments (Φ.map t w) j) ≤ Δ.ℓ ν ↔
      (∑ j,Δ.b ν j*planeMoments w j) ≤ Δ.ℓ ν := by
    have hz (s : ℝ) (hs : s∈Icc (0:ℝ) 1)
        (ha : Δ.ℓ ν-η<∑ j,Δ.b ν j*planeMoments (Φ.map s w) j) :
        HasDerivWithinAt (fun r => ∑ j,Δ.b ν j*planeMoments (Φ.map r w) j) 0 (Icc (0:ℝ) 1) s := by
      have hder := ((hμ ν).differentiable (by simp) (Φ.map s w)).hasFDerivAt.comp_hasDerivAt s (Φ.flow s w)
      have h0 := hzero ν s (Φ.map s w) ha
      rw [fibreHamVF_eq_hamiltonianField hgen,←fibreIsotopy_hamiltonian hgen] at h0
      rw [h0] at hder
      exact hder.hasDerivWithinAt
    have hc : ContinuousOn (fun r => ∑ j,Δ.b ν j*planeMoments (Φ.map r w) j) (Icc (0:ℝ) 1) :=
      ((hμ ν).continuous.comp (Φ.smooth.continuous.comp (continuous_id.prodMk continuous_const))).continuousOn
    have hr := OAI.PackingSufficiencySupport.sublevel_iff_of_zero_in_collar (convex_Icc (0:ℝ) 1)
      hc (by linarith : Δ.ℓ ν-η<Δ.ℓ ν) ht (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num) hz
    simpa only [Φ.zero,Homeomorph.refl_apply,id_eq] using hr
  exact ⟨fun hh => ⟨planeMoments_nonneg _,fun ν => (he ν).1 (hh.2 ν)⟩,
    fun hh => ⟨planeMoments_nonneg _,fun ν => (he ν).2 (hh.2 ν)⟩⟩

theorem fibreIsotopy_preserves_both {D : ComparisonDatum m} {Δ : Polytope m q}
    {P : Moments m → ℝ} {γ : ℝ} (hD : D.Spec Δ P γ) :
    ∀ t∈Icc (0:ℝ) 1,MapsTo ((fibreIsotopy D).map t) (planeMoments ⁻¹' Δ.set) (planeMoments ⁻¹' Δ.set) ∧
      MapsTo ((fibreIsotopy D).map t).symm (planeMoments ⁻¹' Δ.set) (planeMoments ⁻¹' Δ.set) := by
  intro t ht
  refine ⟨fun w hw => (fibreIsotopy_region_iff hD.gen hD.collar t ht w).2 hw,?_⟩
  intro w hw
  apply (fibreIsotopy_region_iff hD.gen hD.collar t ht _).1
  change planeMoments ((fibreIsotopy D).map t (((fibreIsotopy D).map t).symm w))∈region Δ.b Δ.ℓ
  rw [Homeomorph.apply_symm_apply]
  exact hw

/-- The exact lost-mass budget is paid directly by the retained comparison gap. -/
theorem native_surfaceRemainder_nonneg {D : ComparisonDatum m} {Δ : Polytope m q}
    {P A H : Moments m → ℝ} {γ : ℝ} (hD : D.Spec Δ P γ)
    (hH : ∀ p∈Δ.set,A p-D.reserve/16 ≤ H p) {a r : Fin k → ℝ}
    (hra : ∀ i,r i < a i) (hP : ∀ p∈Δ.set,P p ≤ A p-∑ i,max (a i-∑ j,p j) 0) :
    ∀ v,planeMoments v∈Δ.set →
      0 ≤ surfaceRemainder (D.K ∘ planeMoments) (H ∘ planeMoments)
        (fun i => smoothCap a r i ∘ planeMoments) ((fibreIsotopy D).map 1).symm v := by
  intro v hv
  let u := ((fibreIsotopy D).map 1).symm v
  have hu : u∈planeMoments ⁻¹' Δ.set :=
    (fibreIsotopy_preserves_both hD 1 (by norm_num)).2 hv
  have hg := hD.gap u hu
  have hqu : D.qMap u=v := by
    rw [←fibreIsotopy_map_one hD.gen]
    exact Homeomorph.apply_symm_apply _ _
  rw [hqu] at hg
  have hc := sum_smoothCap_le hra (planeMoments v)
  have hp := hP (planeMoments v) hv
  have hm := hH (planeMoments v) hv
  have hr := hD.reserve_le_gap
  have hrp := hD.reserve_pos
  simp only [surfaceRemainder,Function.comp_apply]
  change 0 ≤ D.K (planeMoments u)-D.K (planeMoments v)+H (planeMoments v)-∑ i,smoothCap a r i (planeMoments v)
  linarith
end ToricPackingStages
end SymplecticPacking.HighDim
