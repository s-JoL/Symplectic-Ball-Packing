import SymplecticPacking.HighDim.Handle.RawFullProductFlow

/-!
# Smoothness of the finite-chart full product flow

Smoothness and the coordinate ODE of the native finite-chart flow.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
variable {E M V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M] [T2Space M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]
  {U : Set M}
namespace RawSurfacePresentation
variable (D : RawSurfacePresentation E M U)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem fullMoserFlow_spec
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion)
    (hinj : ∀ x, Injective (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) D.inclusion x))
    (hB : ∀ i, (D.boxes i).box.Smooth)
    (hregular : AmbientRegularity (K:=Plane × V) (D.productInclusion (V:=V)))
    (α : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm D.inclusion (α t)))
    (χ : ℝ × (M × V) → ℝ)
    (hχs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞ χ)
    {G : Set (ℝ × (M × V))} (hG : IsOpen G)
    (hinv : ∀ p ∈ G, (manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α p.1)) p.2).IsInvertible)
    (hχG : tsupport χ ⊆ G)
    (hχcover : ∀ p ∈ tsupport χ, ∃ i, p.2.1 ∈ (D.boxes i).box.chart.source)
    {K : Set (M × V)} (hK : IsCompact K) (hχK : ∀ t x, x ∉ K → χ (t,x)=0) :
    ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,Plane × V) ∞
      (fun p => D.fullMoserFlow α χ p.1 p.2) (Ioo (-2:ℝ) 2 ×ˢ univ) ∧
      (∀ x, D.fullMoserFlow α χ 0 x=x) ∧
      (∀ x t, t ∈ Ioo (-2:ℝ) 2 →
        HasDerivAt (fun s => D.productInclusion (D.fullMoserFlow α χ s x))
          (D.cutFullMoserField α χ (t,D.fullMoserFlow α χ t x)) t) ∧
      ∀ x t, t ∈ Ioo (-2:ℝ) 2 →
        HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,Plane × V) (fun s => D.fullMoserFlow α χ s x) t
          (((1 : ℝ →L[ℝ] ℝ).smulRight (cutField χ
            (fun s => manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α s)))
            (manifoldTimePrimitive (fun s => semanticFullOneForm D.inclusion (α s)))
            (t,D.fullMoserFlow α χ t x))) : ℝ →L[ℝ] (Plane × V)) := by
  let W : (p : ℝ × (M × V)) → TangentSpace 𝓘(ℝ,Plane × V) p.2 :=
    cutField χ (fun s => manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α s)))
      (manifoldTimePrimitive (fun s => semanticFullOneForm D.inclusion (α s)))
  have hW := D.semantic_cut_field_smooth α hα χ hχs hG hinv hχG
  have hWK : ∀ t x, x ∉ K → W (t,x)=0 := by
    intro t x hx
    simp only [W,cutField,hχK t x hx,zero_smul]
  obtain ⟨Φ,Ψ,hΦ,hΨ,hΦ0,hΦinv,hODE,hfix⟩ :=
    exists_spatially_compact_nonautonomous_flow hW hK hWK
  have hsupport {p : ℝ × (M × V)} (hp : χ p ≠ 0) : p ∈ tsupport χ :=
    subset_closure hp
  have hcover : ∀ p, χ p ≠ 0 → ∃ i, p.2.1 ∈ (D.boxes i).box.chart.source :=
    fun p hp => hχcover p (hsupport hp)
  have hInv : ∀ p, χ p ≠ 0 →
      (manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α p.1)) p.2).IsInvertible :=
    fun p hp => hinv p (hχG (hsupport hp))
  have heq (t : ℝ) (ht : t ∈ Ioo (-2:ℝ) 2) (x : M × V) :
      D.fullMoserFlow α χ t x=Φ (t,x) :=
    (D.fullMoserFlow_eq_fieldFlow hι hinj hB hregular α hα χ hcover hInv t x).trans
      (fieldFlow_eq hW hΦ0 hODE ht x)
  have hProdInj : ∀ z : M × V, Injective (mfderiv 𝓘(ℝ,Plane × V) 𝓘(ℝ,E × V) (D.productInclusion (V:=V)) z) := by
    intro z u v h
    rw [D.productInclusion_mfderiv hι] at h
    exact Prod.ext (hinj z.1 (congrArg (fun w : E × V => w.1) h))
      (congrArg (fun w : E × V => w.2) h)
  have hmatch : ∀ p, D.cutFullMoserField α χ p=
      mfderiv 𝓘(ℝ,Plane × V) 𝓘(ℝ,E × V) D.productInclusion p.2 (W p) :=
    fun p => D.cutFullMoserField_eq_cutField hι hB α hα χ p (hcover p) (hInv p)
  refine ⟨hΦ.contMDiffOn.congr (fun p hp => heq p.1 hp.1 p.2),fun x => ?_,?_,?_⟩
  · exact (heq 0 (by norm_num) x).trans (hΦ0 x)
  · intro x t ht
    have hc : IsFieldCurve W x (fun s => Φ (s,x)) := ⟨hΦ0 x,fun s hs => hODE x s hs⟩
    have ha := (ambientFieldCurve_iff (D.productInclusion_contMDiff hι) hProdInj hmatch x _).mpr hc
    have hd := ha.2.2 t ht
    have he : (fun s => D.productInclusion (D.fullMoserFlow α χ s x)) =ᶠ[𝓝 t]
        fun s => D.productInclusion (Φ (s,x)) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      rw [heq s hs x]
    rw [heq t ht x]
    exact hd.congr_of_eventuallyEq he
  · intro x t ht
    have hd := hODE x t ht
    have he : (fun s => D.fullMoserFlow α χ s x) =ᶠ[𝓝 t] fun s => Φ (s,x) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact heq s hs x
    rw [heq t ht x]
    exact hd.congr_of_eventuallyEq he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem fullMoserFlow_diffeomorph
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion)
    (hinj : ∀ x, Injective (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,E) D.inclusion x))
    (hB : ∀ i, (D.boxes i).box.Smooth)
    (hregular : AmbientRegularity (K:=Plane × V) (D.productInclusion (V:=V)))
    (α : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm D.inclusion (α t)))
    (χ : ℝ × (M × V) → ℝ)
    (hχs : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞ χ)
    {G : Set (ℝ × (M × V))} (hG : IsOpen G)
    (hinv : ∀ p ∈ G, (manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α p.1)) p.2).IsInvertible)
    (hχG : tsupport χ ⊆ G)
    (hχcover : ∀ p ∈ tsupport χ, ∃ i, p.2.1 ∈ (D.boxes i).box.chart.source)
    {K : Set (M × V)} (hK : IsCompact K) (hχK : ∀ t x, x ∉ K → χ (t,x)=0) :
    ∃ e : (M × V) ≃ₘ⟮𝓘(ℝ,Plane × V),𝓘(ℝ,Plane × V)⟯ (M × V),
      ⇑e=D.fullMoserFlow α χ 1 := by
  let W : (p : ℝ × (M × V)) → TangentSpace 𝓘(ℝ,Plane × V) p.2 :=
    cutField χ (fun s => manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α s)))
      (manifoldTimePrimitive (fun s => semanticFullOneForm D.inclusion (α s)))
  have hW := D.semantic_cut_field_smooth α hα χ hχs hG hinv hχG
  have hWK : ∀ t x, x ∉ K → W (t,x)=0 := by
    intro t x hx
    simp only [W,cutField,hχK t x hx,zero_smul]
  obtain ⟨Φ,Ψ,hΦ,hΨ,hΦ0,hΦinv,hODE,hfix⟩ :=
    exists_spatially_compact_nonautonomous_flow hW hK hWK
  have hsupport {p : ℝ × (M × V)} (hp : χ p ≠ 0) : p ∈ tsupport χ :=
    subset_closure hp
  have hcover : ∀ p, χ p ≠ 0 → ∃ i, p.2.1 ∈ (D.boxes i).box.chart.source :=
    fun p hp => hχcover p (hsupport hp)
  have hInv : ∀ p, χ p ≠ 0 →
      (manifoldExteriorOneForm (semanticFullOneForm D.inclusion (α p.1)) p.2).IsInvertible :=
    fun p hp => hinv p (hχG (hsupport hp))
  have heq (t : ℝ) (ht : t ∈ Ioo (-2:ℝ) 2) (x : M × V) :
      D.fullMoserFlow α χ t x=Φ (t,x) :=
    (D.fullMoserFlow_eq_fieldFlow hι hinj hB hregular α hα χ hcover hInv t x).trans
      (fieldFlow_eq hW hΦ0 hODE ht x)
  refine ⟨nonautonomousSlice Φ Ψ hΦ hΨ 1 (hΦinv 1 (by norm_num)),?_⟩
  funext x
  exact (heq 1 (by norm_num) x).symm


end RawSurfacePresentation
end SymplecticPacking.HighDim.ToricPackingStages
