import SymplecticPacking.HighDim.Handle.RawSurfaceOperator
import SymplecticPacking.HighDim.Handle.RawManifoldExterior
import SymplecticPacking.HighDim.Handle.RelMoser

/-!
# Native ambient Moser fields and flows

Native ambient Moser fields. Manifold tensors occur only in comparison proofs.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology

/-- The two-coordinate solution of `W(v,·)=-a`. -/
def rawPlanarMoser (W : Plane →L[ℝ] Plane →L[ℝ] ℝ) (a : Plane →L[ℝ] ℝ) : Plane :=
  (-a (0,1) / W (1,0) (0,1), a (1,0) / W (1,0) (0,1))

theorem rawPlanarMoser_spec (W : Plane →L[ℝ] Plane →L[ℝ] ℝ)
    (a : Plane →L[ℝ] ℝ) (hW : ∀ u v, W u v = -W v u)
    (hn : W (1,0) (0,1) ≠ 0) (v : Plane) : W (rawPlanarMoser W a) v = -a v := by
  have hav : a v = v.1 * a (1,0) + v.2 * a (0,1) := by
    have hv : v = v.1 • ((1,0) : Plane) + v.2 • ((0,1) : Plane) := by ext <;> simp
    simpa only [map_add, map_smul, smul_eq_mul] using congrArg a hv
  rw [planar_skew_coefficient W hW]
  simp only [rawPlanarMoser, planarArea_apply]
  rw [hav]
  field_simp [hn]
  <;> ring

theorem planarCoefficient_ne_zero (W : Plane →L[ℝ] Plane →L[ℝ] ℝ)
    (hW : ∀ u v, W u v = -W v u) (hinv : W.IsInvertible)
    (J : Plane →L[ℝ] Plane) (hJ : Surjective J) : W (J (1,0)) (J (0,1)) ≠ 0 := by
  intro hz
  have hzero : W = 0 := by
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨s,rfl⟩ := hJ u
    obtain ⟨t,rfl⟩ := hJ v
    have he := planar_skew_coefficient (W.bilinearComp J J) (fun u v => hW _ _) s t
    simpa only [ContinuousLinearMap.bilinearComp_apply,hz,zero_mul,zero_apply] using he
  obtain ⟨e,he⟩ := hinv
  have hbad : ((1,0) : Plane) = 0 := e.injective (by
    change (e : Plane →L[ℝ] Plane →L[ℝ] ℝ) (1,0) =
      (e : Plane →L[ℝ] Plane →L[ℝ] ℝ) 0
    rw [he,hzero]
    rfl)
  have hh := congrArg Prod.fst hbad
  norm_num at hh

theorem fold_first_eq {I : Type} {E : Type} [Zero E] (l : List I)
    (P : I → Prop) [DecidablePred P] (f : I → E) (v : E)
    (hlocal : ∀ i ∈ l, P i → f i = v) (hnone : (¬ ∃ i ∈ l, P i) → v = 0) :
    l.foldr (fun i rest => if P i then f i else rest) 0 = v := by
  induction l with
  | nil => exact (hnone (by simp)).symm
  | cons i l ih =>
    by_cases hi : P i
    · simpa only [List.foldr_cons,if_pos hi] using hlocal i (by simp) hi
    · simp only [List.foldr_cons,if_neg hi]
      apply ih
      · exact fun j hj => hlocal j (by simp [hj])
      · intro hn
        apply hnone
        rintro ⟨j,hj,hP⟩
        rcases List.mem_cons.mp hj with rfl | hj
        · exact hi hP
        · exact hn ⟨j,hj,hP⟩

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M]

namespace RawAmbientBox
/-- Solve in the fixed linear coordinate, then apply the displayed inverse-chart derivative.
This formula never inspects a semantic tangent-space trivialisation. -/
def moserField (B : RawAmbientBox E M)
    (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) (α : M → E →L[ℝ] ℝ) (x : M) : E :=
  let J := B.frame (B.box.chart x)
  J (rawPlanarMoser ((Ω x).bilinearComp J J) ((α x).comp J))

theorem moserField_contraction (B : RawAmbientBox E M)
    (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) (α : M → E →L[ℝ] ℝ) (x : M)
    (hΩ : ∀ u v, Ω x u v = -Ω x v u)
    (hn : Ω x (B.frame (B.box.chart x) (1,0))
      (B.frame (B.box.chart x) (0,1)) ≠ 0) (v : Plane) :
    Ω x (B.moserField Ω α x) (B.frame (B.box.chart x) v) =
      -α x (B.frame (B.box.chart x) v) := by
  exact rawPlanarMoser_spec ((Ω x).bilinearComp (B.frame (B.box.chart x))
    (B.frame (B.box.chart x))) ((α x).comp (B.frame (B.box.chart x)))
    (fun u v => hΩ _ _) hn v

/-- Coordinate independence follows from the two-dimensional contraction equation.
All semantic tangent information is confined to this proposition. -/
theorem moserField_eq_of_contraction (B : RawAmbientBox E M)
    (Ω : M → E →L[ℝ] E →L[ℝ] ℝ) (α : M → E →L[ℝ] ℝ) (x : M)
    (A : Plane →L[ℝ] E) (J : Plane →L[ℝ] Plane)
    (hframe : B.frame (B.box.chart x) = A.comp J) (hJ : Surjective J)
    (hΩ : ∀ u v, Ω x u v = -Ω x v u)
    (hn : Ω x (B.frame (B.box.chart x) (1,0))
      (B.frame (B.box.chart x) (0,1)) ≠ 0)
    (hinv : ((Ω x).bilinearComp A A).IsInvertible) (V : Plane)
    (hV : ∀ v, Ω x (A V) (A v) = -α x (A v)) :
    B.moserField Ω α x = A V := by
  let u := rawPlanarMoser
    ((Ω x).bilinearComp (B.frame (B.box.chart x)) (B.frame (B.box.chart x)))
    ((α x).comp (B.frame (B.box.chart x)))
  have he : ((Ω x).bilinearComp A A) (J u) = ((Ω x).bilinearComp A A) V := by
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, rfl⟩ := hJ v
    have hc := B.moserField_contraction Ω α x hΩ hn w
    change Ω x (B.frame (B.box.chart x) u) (B.frame (B.box.chart x) w) =
      -α x (B.frame (B.box.chart x) w) at hc
    rw [hframe] at hc
    exact hc.trans (hV (J w)).symm
  obtain ⟨e, hee⟩ := hinv
  have hu : J u = V := e.injective (by rw [← hee] at he; exact he)
  change B.frame (B.box.chart x) u = A V
  rw [hframe, ContinuousLinearMap.comp_apply, hu]
end RawAmbientBox

section semanticField
variable [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem RawAmbientBox.frame_eq_mfderiv_comp (B : RawAmbientBox E M)
    {ι : M → E} (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι)
    (hinc : B.inclusion = ι) (hB : B.box.Smooth)
    {y : Plane} (hy : y ∈ B.box.chart.target) :
    B.frame y = (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι (B.box.chart.symm y)).comp
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) B.box.chart.symm y) := by
  have hc := ((hB.inverse y hy).contMDiffAt (B.box.chart.open_target.mem_nhds hy)).mdifferentiableAt (by simp)
  have hd := ((hι.mdifferentiable (by simp) _).hasMFDerivAt.comp y hc.hasMFDerivAt).mfderiv
  have he : B.inverseAmbient = ι ∘ B.box.chart.symm := by funext z; exact congrFun hinc _
  unfold RawAmbientBox.frame
  rw [he]
  rw [mfderiv_eq_fderiv] at hd
  exact hd

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem RawAmbientBox.moserField_eq_manifoldMoserField (B : RawAmbientBox E M)
    {ι : M → E} (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι)
    (hinc : B.inclusion = ι) (hB : B.box.Smooth)
    (Ω : ℝ → M → E →L[ℝ] E →L[ℝ] ℝ) (α : ℝ → M → E →L[ℝ] ℝ)
    (p : ℝ × M) (hx : p.2 ∈ B.box.chart.source)
    (hΩ : ∀ u v, Ω p.1 p.2 u v = -Ω p.1 p.2 v u)
    (hinv : (semanticTwoForm ι (Ω p.1) p.2).IsInvertible) :
    B.moserField (Ω p.1) (α p.1) p.2 =
      mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι p.2
        (manifoldMoserField (fun t => semanticTwoForm ι (Ω t))
          (fun t => semanticOneForm ι (α t)) p) := by
  let z := B.box.chart p.2
  have hz : z ∈ B.box.chart.target := B.box.chart.map_source hx
  have hxz : B.box.chart.symm z = p.2 := B.box.chart.left_inv hx
  let J := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) B.box.chart.symm z
  let L := mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) B.box.chart p.2
  let e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) M Plane ∞ :=
    { toPartialEquiv := B.box.chart.toPartialEquiv
      open_source := B.box.chart.open_source
      open_target := B.box.chart.open_target
      contMDiffOn_toFun := hB.forward
      contMDiffOn_invFun := hB.inverse }
  have hJL : J.comp L = ContinuousLinearMap.id ℝ Plane := handle_mfderiv_symm_comp e hx
  have hJ : Surjective J := fun v => ⟨L v,congrArg (fun D : Plane →L[ℝ] Plane => D v) hJL⟩
  have hc := ((hB.inverse z hz).contMDiffAt (B.box.chart.open_target.mem_nhds hz)).mdifferentiableAt (by simp)
  have hd := ((hι.mdifferentiable (by simp) _).hasMFDerivAt.comp z hc.hasMFDerivAt).mfderiv
  have he : B.inverseAmbient = ι ∘ B.box.chart.symm := by funext y; exact congrFun hinc _
  have hframe : B.frame z = (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι p.2).comp J := by
    unfold RawAmbientBox.frame
    rw [he]
    rw [mfderiv_eq_fderiv] at hd
    change fderiv ℝ (ι ∘ B.box.chart.symm) z =
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) ι (B.box.chart.symm z)).comp J at hd
    rw [hxz] at hd
    exact hd
  have hn : Ω p.1 p.2 (B.frame z (1,0)) (B.frame z (0,1)) ≠ 0 := by
    rw [hframe]
    exact planarCoefficient_ne_zero (semanticTwoForm ι (Ω p.1) p.2)
      (fun u v => hΩ _ _) hinv J hJ
  apply B.moserField_eq_of_contraction (Ω p.1) (α p.1) p.2 _ J hframe hJ hΩ hn hinv
  intro v
  have hs : semanticTwoForm ι (Ω p.1) p.2
      (manifoldMoserField (fun t => semanticTwoForm ι (Ω t))
        (fun t => semanticOneForm ι (α t)) p) = -semanticOneForm ι (α p.1) p.2 := by
    simp only [manifoldMoserField,map_neg,hinv.self_apply_inverse]
  exact congrArg (fun a : Plane →L[ℝ] ℝ => a v) hs

end semanticField

namespace RawSurfacePresentation
variable [T2Space M] {U : Set M} (D : RawSurfacePresentation E M U)

/-- A finite, explicitly weighted ambient field. The guard keeps all chart operations
inside their stated source; weights already vanish outside the smaller carrier. -/
def moserField (Ω : ℝ → M → E →L[ℝ] E →L[ℝ] ℝ)
    (α : ℝ → M → E →L[ℝ] ℝ) (p : ℝ × M) : E := by
  classical
  exact ∑ i, D.partitionWeight i p.2 •
    (if p.2 ∈ (D.boxes i).box.chart.source then
      (D.boxes i).moserField (Ω p.1) (α p.1) p.2 else 0)

/-- Use the first chart containing the point. On overlaps the explicit local solutions
coincide, so evaluating in any certified chart gives exactly the same vector. -/
def chartMoserField (Ω : ℝ → M → E →L[ℝ] E →L[ℝ] ℝ)
    (α : ℝ → M → E →L[ℝ] ℝ) (p : ℝ × M) : E := by
  classical
  exact (List.finRange (D.size+1)).foldr (fun i rest =>
    if p.2 ∈ (D.boxes i).box.chart.source then
      (D.boxes i).moserField (Ω p.1) (α p.1) p.2 else rest) 0

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem chartMoserField_eq_manifoldMoserField
    [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion)
    (hB : ∀ i, (D.boxes i).box.Smooth)
    (Ω : ℝ → M → E →L[ℝ] E →L[ℝ] ℝ) (α : ℝ → M → E →L[ℝ] ℝ)
    (p : ℝ × M) (hΩ : ∀ u v, Ω p.1 p.2 u v = -Ω p.1 p.2 v u)
    (hinv : (semanticTwoForm D.inclusion (Ω p.1) p.2).IsInvertible)
    (hα : (∀ i, p.2 ∉ (D.boxes i).box.chart.source) → α p.1 p.2 = 0) :
    D.chartMoserField Ω α p = mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) D.inclusion p.2
      (manifoldMoserField (fun t => semanticTwoForm D.inclusion (Ω t))
        (fun t => semanticOneForm D.inclusion (α t)) p) := by
  classical
  unfold chartMoserField
  apply fold_first_eq
  · intro i _ hi
    exact (D.boxes i).moserField_eq_manifoldMoserField hι (D.box_inclusion i)
      (hB i) Ω α p hi hΩ hinv
  · intro hn
    have hz : α p.1 p.2 = 0 := hα (fun i hi => hn ⟨i,by simp,hi⟩)
    have hs : semanticOneForm D.inclusion (α p.1) p.2 = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      change α p.1 p.2 _ = 0
      rw [hz]
      rfl
    simp only [manifoldMoserField,hs,map_zero,neg_zero]

end RawSurfacePresentation

section ambientFlow
variable {K : Type} [NormedAddCommGroup K] [NormedSpace ℝ K]
  [ChartedSpace K M] [IsManifold 𝓘(ℝ,K) ∞ M]

/-- An integral curve specified by its ambient coordinates. Differentiability of
the manifold-valued path is a regularity condition, not a supplied solution. -/
def IsAmbientFieldCurve (ι : M → E) (F : ℝ × M → E) (x : M) (γ : ℝ → M) : Prop :=
  γ 0 = x ∧ MDifferentiableOn 𝓘(ℝ,ℝ) 𝓘(ℝ,K) γ (Ioo (-2:ℝ) 2) ∧
    ∀ t ∈ Ioo (-2:ℝ) 2, HasDerivAt (fun s => ι (γ s)) (F (t,γ t)) t

open Classical in
/-- The unique endpoint of the ambient-coordinate ODE, with the initial point as fallback.
No abstract manifold vector field is an input to this definition. -/
def ambientFieldFlow (ι : M → E) (F : ℝ × M → E) (t : ℝ) (x : M) : M :=
  if h : ∃! y, ∃ γ, IsAmbientFieldCurve (K := K) ι F x γ ∧ γ t = y then Explicit.the h else x

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem ambientFieldCurve_iff {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,K) 𝓘(ℝ,E) ∞ ι)
    (hinj : ∀ x, Injective (mfderiv 𝓘(ℝ,K) 𝓘(ℝ,E) ι x))
    {F : ℝ × M → E} {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,K) p.2}
    (hFV : ∀ p, F p = mfderiv 𝓘(ℝ,K) 𝓘(ℝ,E) ι p.2 (V p))
    (x : M) (γ : ℝ → M) : IsAmbientFieldCurve (K := K) ι F x γ ↔ IsFieldCurve V x γ := by
  constructor
  · rintro ⟨h0,hγ,hODE⟩
    refine ⟨h0,fun t ht => ?_⟩
    have hc := (hγ t ht).mdifferentiableAt (isOpen_Ioo.mem_nhds ht)
    have hd := ((hι.mdifferentiable (by simp) _).hasMFDerivAt.comp t hc.hasMFDerivAt).hasFDerivAt
    have he := hd.unique (hODE t ht).hasFDerivAt
    have hv : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,K) γ t 1 = V (t,γ t) := by
      apply hinj (γ t)
      have hh := congrArg (fun A : ℝ →L[ℝ] E => A 1) he
      change (mfderiv 𝓘(ℝ,K) 𝓘(ℝ,E) ι (γ t))
        (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,K) γ t 1) = (1:ℝ) • F (t,γ t) at hh
      simpa only [one_smul,hFV] using hh
    have hD : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,K) γ t =
        (1 : ℝ →L[ℝ] ℝ).smulRight (V (t,γ t)) := by
      let D : ℝ →L[ℝ] K := mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,K) γ t
      let v : K := V (t,γ t)
      have hv' : D 1 = v := hv
      have he' : D = (1 : ℝ →L[ℝ] ℝ).smulRight v := by
        rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton,← hv',
          ContinuousLinearMap.toSpanSingleton_apply_map_one]
      exact he'
    exact hD ▸ hc.hasMFDerivAt
  · rintro ⟨h0,hODE⟩
    refine ⟨h0,fun t ht => (hODE t ht).mdifferentiableAt.mdifferentiableWithinAt,fun t ht => ?_⟩
    have hd := ((hι.mdifferentiable (by simp) _).hasMFDerivAt.comp t (hODE t ht)).hasFDerivAt.hasDerivAt
    change HasDerivAt (fun s => ι (γ s))
      ((mfderiv 𝓘(ℝ,K) 𝓘(ℝ,E) ι (γ t)) ((1:ℝ) • V (t,γ t))) t at hd
    simpa only [one_smul,← hFV (t,γ t)] using hd

theorem ambientFieldFlow_eq_fieldFlow {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,K) 𝓘(ℝ,E) ∞ ι)
    (hinj : ∀ x, Injective (mfderiv 𝓘(ℝ,K) 𝓘(ℝ,E) ι x))
    {F : ℝ × M → E} {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ,K) p.2}
    (hFV : ∀ p, F p = mfderiv 𝓘(ℝ,K) 𝓘(ℝ,E) ι p.2 (V p))
    (t : ℝ) (x : M) : ambientFieldFlow (K := K) ι F t x = fieldFlow V t x := by
  have he : IsAmbientFieldCurve (K := K) ι F x = IsFieldCurve V x := by
    funext γ
    exact propext (ambientFieldCurve_iff hι hinj hFV x γ)
  unfold ambientFieldFlow fieldFlow
  rw [he]

end ambientFlow

#check_explicit rawPlanarMoser
#check_explicit RawAmbientBox.moserField
#check_explicit RawSurfacePresentation.moserField
#check_explicit RawSurfacePresentation.chartMoserField
#check_explicit ambientFieldFlow
end SymplecticPacking.HighDim.ToricPackingStages
