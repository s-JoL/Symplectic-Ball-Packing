import SymplecticPacking.HighDim.Model
import SymplecticPacking.Explicit
import OAI.Geometry.BallPacking.Hamiltonian.AnnularDensityMass
import OAI.Geometry.BallPacking.Moser.ManifoldExteriorNaturality
import OAI.Geometry.BallPacking.Flows.NonautonomousManifoldFlow

/-!
# Relative Moser maps as explicit flows (paper thm:mech-packing, `Φ`)

Explicit version of the OpenAI library's `toric_redistribution_moser`
(`Hamiltonian/AnnularDensityMass.lean`), whose map is the time-one map of an existentially
chosen cut-off Moser field (`exists_joint_localized_manifold_moser_field`,
`exists_base_moser_cutoff`) integrated by an existential flow
(`exists_spatially_compact_nonautonomous_flow`).

Here:
* `fieldFlow V t x` is the value at `t` of the *unique* integral curve of the time-dependent
  field `V` on `(-2, 2)` through `x` at time `0` (definite description `Explicit.the`);
* `diffeoOf f` is *the* diffeomorphism with underlying map `f` (definite description;
  identity if there is none);
* `cutField χ Ω α = χ • moserVec Ω α` for an explicit cutoff `χ`, where `moserVec` is the
  unique solution `v` of `Ω v = −α` (definite description).

`cutMoser_spec` (generic, any manifold): if `χ` is smooth, supported where `Ω` is invertible,
equal to one near `[0,1] × D` (`D` a compact sublevel set with collar-tangent faces) and the
field is spatially compactly supported, then `diffeoOf (fieldFlow (cutField χ Ω α) 1)` maps `D`
onto `D`, `int D` onto `int D`, and pulls `Ω 1` back to `Ω 0` on `D`. The proof follows the
library's `manifold_relative_sublevel_moser`, with the library flow identified with
`fieldFlow` by uniqueness of integral curves.

The section `horizontal` specializes this to the product primitives `θ + Γ(t, ·)` on `M × V`
(`horizontalMoserMap`), and the section `toric` to the linear path between two toric
primitives (`toricMoserMap`, `toricMoserMap_spec`). The section `model` records the standing
hypotheses `TargetPrimitive` on a target primitive of a toric model and the positivity of the
base coefficients of the model and target primitives.
-/

noncomputable section

namespace SymplecticPacking.HighDim.ToricPackingStages

open Set Function Manifold Filter
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology

section generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- `γ` is an integral curve on `(-2, 2)` of the time-dependent field `V`, starting at `x`. -/
def IsFieldCurve (V : (p : ℝ × M) → TangentSpace 𝓘(ℝ, E) p.2) (x : M) (γ : ℝ → M) : Prop :=
  γ 0 = x ∧ ∀ t ∈ Ioo (-2 : ℝ) 2, HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t
    ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t, γ t)))

open Classical in
/-- The time-`t` map of the field `V`: the value at `t` of the unique integral curve through
`x` (definite description; `x` itself if the curve is not unique). -/
def fieldFlow (V : (p : ℝ × M) → TangentSpace 𝓘(ℝ, E) p.2) (t : ℝ) (x : M) : M :=
  if h : ∃! y, ∃ γ, IsFieldCurve V x γ ∧ γ t = y then Explicit.the h else x

open Classical in
/-- The diffeomorphism with underlying map `f` (definite description; the identity if `f` is
not a diffeomorphism). -/
def diffeoOf [IsManifold 𝓘(ℝ, E) ∞ M] (f : M → M) : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M :=
  if h : ∃! e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M, ⇑e = f then Explicit.the h
  else Diffeomorph.refl 𝓘(ℝ, E) M ∞

open Classical in
/-- The Moser vector: the unique `v` with `Ω_t(x) v = −α_t(x)` (definite description; `0`
where it is not unique). -/
def moserVec (Ω : ℝ → ManifoldTwoForm E M) (α : ℝ → ManifoldOneForm E M) (p : ℝ × M) :
    TangentSpace 𝓘(ℝ, E) p.2 :=
  if h : ∃! v : E, Ω p.1 p.2 v = -α p.1 p.2 then Explicit.the h else 0

/-- The cut-off Moser field `χ • (−Ω⁻¹ α)`. -/
def cutField (χ : ℝ × M → ℝ) (Ω : ℝ → ManifoldTwoForm E M) (α : ℝ → ManifoldOneForm E M)
    (p : ℝ × M) : TangentSpace 𝓘(ℝ, E) p.2 :=
  χ p • moserVec Ω α p

/-- The same field written with the library's Moser field (used in proofs only). -/
def cutFieldInv (χ : ℝ × M → ℝ) (Ω : ℝ → ManifoldTwoForm E M) (α : ℝ → ManifoldOneForm E M)
    (p : ℝ × M) : TangentSpace 𝓘(ℝ, E) p.2 :=
  χ p • manifoldMoserField Ω α p

theorem moserVec_eq {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M} {p : ℝ × M}
    (hinv : (Ω p.1 p.2).IsInvertible) : moserVec Ω α p = manifoldMoserField Ω α p := by
  have hs : Ω p.1 p.2 (manifoldMoserField Ω α p) = -α p.1 p.2 := by
    simp only [manifoldMoserField, map_neg, hinv.self_apply_inverse]
  have hu : ∃! v : E, Ω p.1 p.2 v = -α p.1 p.2 := by
    refine ⟨_, hs, fun w hw => ?_⟩
    obtain ⟨e, he⟩ := hinv
    apply e.injective
    change (e : E →L[ℝ] E →L[ℝ] ℝ) w = (e : E →L[ℝ] E →L[ℝ] ℝ) (manifoldMoserField Ω α p)
    rw [he, hw, hs]
  unfold moserVec
  rw [dif_pos hu]
  exact Explicit.the_eq hu hs

theorem cutField_eq_inv {χ : ℝ × M → ℝ} {Ω : ℝ → ManifoldTwoForm E M}
    {α : ℝ → ManifoldOneForm E M} {U : Set (ℝ × M)} (hinv : ∀ p ∈ U, (Ω p.1 p.2).IsInvertible)
    (hχU : tsupport χ ⊆ U) : cutField χ Ω α = cutFieldInv χ Ω α := by
  funext p
  unfold cutField cutFieldInv
  by_cases hp : p ∈ U
  · rw [moserVec_eq (hinv p hp)]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hp (hχU h)), zero_smul, zero_smul]

theorem diffeoOf_eq [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → M}
    (e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M) (he : ⇑e = f) : diffeoOf f = e := by
  have h : ∃! e' : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M, ⇑e' = f :=
    ⟨e, he, fun e' h' => Diffeomorph.ext (fun x => by rw [h', he])⟩
  unfold diffeoOf
  rw [dif_pos h]
  exact Explicit.the_eq h he

theorem fieldFlow_eq [FiniteDimensional ℝ E] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {V : (p : ℝ × M) → TangentSpace 𝓘(ℝ, E) p.2}
    (hV : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞
      (fun p => (⟨p.2, V p⟩ : TangentBundle 𝓘(ℝ, E) M)))
    {Φ : ℝ × M → M} (h0 : ∀ x, Φ (0, x) = x)
    (hODE : ∀ x t, t ∈ Ioo (-2 : ℝ) 2 → HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
      (fun s => Φ (s, x)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t, Φ (t, x)))))
    {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) (x : M) : fieldFlow V t x = Φ (t, x) := by
  have hc : IsFieldCurve V x (fun s => Φ (s, x)) := ⟨h0 x, fun s hs => hODE x s hs⟩
  have hu : ∃! y, ∃ γ, IsFieldCurve V x γ ∧ γ t = y := by
    refine ⟨Φ (t, x), ⟨_, hc, rfl⟩, ?_⟩
    rintro y ⟨γ, hγ, rfl⟩
    exact nonautonomous_curve_eqOn hV (show (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 by norm_num)
      hγ.2 hc.2 (hγ.1.trans (h0 x).symm) ht
  unfold fieldFlow
  rw [dif_pos hu]
  exact Explicit.the_eq hu ⟨_, hc, rfl⟩

/-- Smoothness of the cut-off Moser field (as in the library's
`exists_joint_localized_manifold_moser_field`, with the cutoff given). -/
theorem cutField_smooth [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ, E) c).target))
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ, E) c).target))
    {U : Set (ℝ × M)} (hU : IsOpen U)
    (hinv : ∀ p ∈ U, (Ω p.1 p.2).IsInvertible)
    {χ : ℝ × M → ℝ} (hχs : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ χ)
    (hχU : tsupport χ ⊆ U) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞
      (fun p => (⟨p.2, cutFieldInv χ Ω α p⟩ : TangentBundle 𝓘(ℝ, E) M)) := by
  have he (c : M) (q : ℝ × E) : timeChartField (cutFieldInv χ Ω α) c q =
      χ (q.1, (extChartAt 𝓘(ℝ, E) c).symm q.2) •
        timeChartField (manifoldMoserField Ω α) c q := by
    dsimp only [timeChartField, cutFieldInv]
    exact (chartDifferential c _).map_smul _ _
  apply timeField_smooth_of_coordinates
  intro p
  let c := p.2
  let q : ℝ × E := (p.1, extChartAt 𝓘(ℝ, E) c c)
  let F : ℝ × E → ℝ × M := fun z => (z.1, (extChartAt 𝓘(ℝ, E) c).symm z.2)
  have hq : q.2 ∈ (extChartAt 𝓘(ℝ, E) c).target := mem_extChartAt_target c
  have hFe : F q = p := by dsimp only [F, q, c]; rw [extChartAt_to_inv]
  have hi : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (extChartAt 𝓘(ℝ, E) c).symm q.2 :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E)) (n := ∞) c).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) c).mem_nhds hq)
  have hF : ContMDiffAt 𝓘(ℝ, ℝ × E) ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) ∞ F q :=
    contDiffAt_fst.contMDiffAt.prodMk (hi.comp q contDiffAt_snd.contMDiffAt)
  have hn : (univ ×ˢ (extChartAt 𝓘(ℝ, E) c).target) ∈ 𝓝 q :=
    (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) c)).mem_nhds ⟨mem_univ _, hq⟩
  by_cases hp : p ∈ U
  · have hnU : ∀ᶠ z in 𝓝 q, F z ∈ U := hF.continuousAt.preimage_mem_nhds
      (by rw [hFe]; exact hU.mem_nhds hp)
    have hs := timeChartField_moser_contDiffAt hq ((hΩ c).contDiffAt hn)
      ((hα c).contDiffAt hn) (hnU.mono fun z hz => hinv (F z) hz)
    have hc : ContDiffAt ℝ ∞ (fun z => χ (F z)) q :=
      (hχs.contMDiffAt.comp q hF).contDiffAt
    exact (hc.smul hs).congr_of_eventuallyEq (Filter.Eventually.of_forall (he c))
  · have hp' : p ∉ tsupport χ := fun h => hp (hχU h)
    have hz : ∀ᶠ z in 𝓝 q, χ (F z) = 0 := by
      have hh : F ⁻¹' (tsupport χ)ᶜ ∈ 𝓝 q := hF.continuousAt.preimage_mem_nhds
        (show (tsupport χ)ᶜ ∈ 𝓝 (F q) by
          rw [hFe]; exact (isClosed_tsupport χ).isOpen_compl.mem_nhds hp')
      filter_upwards [hh] with z hz
      exact image_eq_zero_of_notMem_tsupport hz
    apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
    filter_upwards [hz] with z hz
    rw [he, hz, zero_smul]

/-- **Explicit relative Moser map** (generic form of the library's
`manifold_relative_sublevel_moser`, for the explicit field `cutField χ Ω α` and the explicit
map `diffeoOf (fieldFlow · 1)`). -/
theorem matchedMoser_spec [FiniteDimensional ℝ E] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ, E) c).target))
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ, E) c).target))
    {ι : Type*} (μ : ι → M → ℝ)
    (hμ : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i, a i < c i)
    {U : Set (ℝ × M)} (hU : IsOpen U)
    (hDU : Icc (0 : ℝ) 1 ×ˢ {x | ∀ i, μ i x ≤ c i} ⊆ U)
    (hinv : ∀ p ∈ U, (Ω p.1 p.2).IsInvertible)
    (hskew : ∀ p ∈ U, ∀ v w, Ω p.1 p.2 v w = -Ω p.1 p.2 w v)
    (hclosed : ∀ t b y, y ∈ (extChartAt 𝓘(ℝ, E) b).target →
      (t, (extChartAt 𝓘(ℝ, E) b).symm y) ∈ U → ∀ u v w,
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) b q.2) (t, y) (0, u) v w -
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) b q.2) (t, y) (0, v) u w +
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) b q.2) (t, y) (0, w) u v = 0)
    (htime : ∀ t b y, y ∈ (extChartAt 𝓘(ℝ, E) b).target →
      (t, (extChartAt 𝓘(ℝ, E) b).symm y) ∈ U → ∀ v w,
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) b q.2) (t, y) (1, 0) v w =
      fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) b q.2) (t, y) (0, v) w -
      fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) b q.2) (t, y) (0, w) v)
    (Z : ι → M → E)
    (hface : ∀ i p, p ∈ U → a i < μ i p.2 →
      α p.1 p.2 = 0 ∨
      (Ω p.1 p.2 (Z i p.2) = -mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (μ i) p.2 ∧
        α p.1 p.2 (Z i p.2) = 0))
    {χ : ℝ × M → ℝ} (hχs : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ χ)
    (hχU : tsupport χ ⊆ U)
    (hmatch : ∀ᶠ p in 𝓝ˢ (Icc (0 : ℝ) 1 ×ˢ {x | ∀ i, μ i x ≤ c i}),
      χ p • manifoldMoserField Ω α p = manifoldMoserField Ω α p)
    (hχC : ∃ C : Set M, IsCompact C ∧ ∀ t x, x ∉ C → χ (t, x) = 0 ∨ α t x = 0) :
    diffeoOf (E := E) (fieldFlow (cutField χ Ω α) 1) '' {x | ∀ i, μ i x ≤ c i} =
        {x | ∀ i, μ i x ≤ c i} ∧
      diffeoOf (E := E) (fieldFlow (cutField χ Ω α) 1) '' interior {x | ∀ i, μ i x ≤ c i} =
        interior {x | ∀ i, μ i x ≤ c i} ∧
      PreservesTwoFormOn (diffeoOf (E := E) (fieldFlow (cutField χ Ω α) 1)) (Ω 0) (Ω 1)
        {x | ∀ i, μ i x ≤ c i} ∧
      (∀ x, (∀ t, α t x = 0) → diffeoOf (E := E) (fieldFlow (cutField χ Ω α) 1) x = x) := by
  rw [cutField_eq_inv hinv hχU]
  set V := cutFieldInv χ Ω α with hVdef
  have hV : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞
      (fun p => (⟨p.2, V p⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    cutField_smooth hΩ hα hU hinv hχs hχU
  have hVe : ∀ᶠ p in 𝓝ˢ (Icc (0 : ℝ) 1 ×ˢ {x | ∀ i, μ i x ≤ c i}),
      V p = manifoldMoserField Ω α p := hmatch
  have hVz : ∀ p, α p.1 p.2 = 0 → V p = 0 := by
    intro p hp
    change χ p • (-((Ω p.1 p.2).inverse (α p.1 p.2))) = 0
    rw [hp, map_zero, neg_zero, smul_zero]
  obtain ⟨C, hC, hχC⟩ := hχC
  have hVC : ∀ s x, x ∉ C → V (s, x) = 0 := by
    intro s x hx
    rcases hχC s x hx with h | h
    · change χ (s, x) • _ = 0
      rw [h, zero_smul]
    · exact hVz (s, x) h
  have hVtan : ∀ p (L : E →L[ℝ] ℝ), (p ∈ U → L (manifoldMoserField Ω α p) = 0) →
      L (V p) = 0 := by
    intro p L hL
    change L (χ p • manifoldMoserField Ω α p) = 0
    erw [map_smul]
    by_cases hp : p ∈ U
    · rw [hL hp, smul_zero]
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hp (hχU h)), zero_smul]
  obtain ⟨Φ, Ψ, hΦ, hΨ, hΦ0, hΦinv, hODE, hfix⟩ :=
    exists_spatially_compact_nonautonomous_flow hV hC hVC
  have htangent (i : ι) (t : ℝ) (x : M) (hx : a i < μ i x) :
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (μ i) x (V (t, x)) = 0 := by
    apply hVtan
    intro hp
    rcases hface i (t, x) hp hx with hz | ⟨hm, hh⟩
    · simp only [manifoldMoserField, hz, map_zero, neg_zero]
      exact (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (μ i) x).map_zero
    · exact manifoldMoserField_moment_tangent (hinv (t, x) hp) (hskew (t, x) hp)
        _ (Z i x) hm hh
  have hiff (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (x : M) :
      (∀ i, μ i (Φ (t, x)) ≤ c i) ↔ (∀ i, μ i x ≤ c i) := by
    apply manifold_flow_sublevels_iff hΦ hΦ0 _ μ hμ a c hac htangent t ht x
    intro y s hs
    exact hODE y s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- the explicit map is the library flow at time one
  let e : M ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ M := nonautonomousSlice Φ Ψ hΦ hΨ 1 (hΦinv 1 h1)
  have hflow : fieldFlow V 1 = fun x => Φ (1, x) := by
    funext x
    exact fieldFlow_eq hV hΦ0 hODE (show (1 : ℝ) ∈ Ioo (-2 : ℝ) 2 by norm_num) x
  have hde : diffeoOf (E := E) (fieldFlow V 1) = e := diffeoOf_eq e (by rw [hflow]; rfl)
  rw [hde]
  have himg := manifold_flow_image_sublevels hΦ hΨ 1 (hΦinv 1 h1)
    (D := {x | ∀ i, μ i x ≤ c i}) (hiff 1 h1)
  refine ⟨himg.1, himg.2, ?_, ?_⟩
  · intro x hx v w
    have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        HasDerivAt (fun r => manifoldPullback Φ Ω r x v w) 0 s := by
      apply local_manifold_form_transport_derivative hΦ hV isOpen_Ioo hODE hΩ
        (show s ∈ Ioo (-2 : ℝ) 2 by constructor <;> linarith [hs.1, hs.2]) x
      intro b y hy he
      have hpK : (s, (extChartAt 𝓘(ℝ, E) b).symm y) ∈
          Icc (0 : ℝ) 1 ×ˢ {x | ∀ i, μ i x ≤ c i} :=
        ⟨hs, by rw [he]; exact (hiff s hs x).mpr hx⟩
      have hpU := hDU hpK
      have hn : (univ ×ˢ (extChartAt 𝓘(ℝ, E) b).target) ∈ 𝓝 (s, y) :=
        (isOpen_univ.prod (isOpen_extChartAt_target (I := 𝓘(ℝ, E)) b)).mem_nhds
          ⟨mem_univ _, hy⟩
      apply joint_manifold_moser_PDE hV hU hy hpU hinv
        (hVe.filter_mono (nhds_le_nhdsSet hpK)) ((hΩ b).contDiffAt hn)
        ((hα b).contDiffAt hn) _ (hclosed s b y hy hpU) (htime s b y hy hpU)
      intro u z
      exact hskew _ hpU _ _
    have hE := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hd s hs).hasDerivWithinAt)
      (fun s hs => (by simp : ‖(0 : ℝ)‖ ≤ (0 : ℝ)))
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num) h1
    have hconst : manifoldPullback Φ Ω 1 x v w = manifoldPullback Φ Ω 0 x v w := by
      simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hE
    have hid : (fun y => Φ (0, y)) = id := funext hΦ0
    have hDifferential : preferredDifferential (E := E) (fun y => Φ (0, y)) x =
        ContinuousLinearMap.id ℝ E := by
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y => Φ (0, y)) x = _
      rw [hid]
      exact mfderiv_id
    have h0 : manifoldPullback Φ Ω 0 x v w = Ω 0 x v w := by
      rw [manifoldPullback, hDifferential]
      simp only [hΦ0]
      rfl
    exact hconst.trans h0
  · intro x hx
    exact hfix x (fun s => hVz (s, x) (hx s)) 1

theorem cutMoser_spec [FiniteDimensional ℝ E] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {Ω : ℝ → ManifoldTwoForm E M} {α : ℝ → ManifoldOneForm E M}
    (hΩ : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartTwoForm (Ω q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ, E) c).target))
    (hα : ∀ c, ContDiffOn ℝ ∞ (fun q : ℝ × E => chartOneForm (α q.1) c q.2)
      (univ ×ˢ (extChartAt 𝓘(ℝ, E) c).target))
    {ι : Type*} (μ : ι → M → ℝ)
    (hμ : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i, a i < c i)
    {U : Set (ℝ × M)} (hU : IsOpen U)
    (hDU : Icc (0 : ℝ) 1 ×ˢ {x | ∀ i, μ i x ≤ c i} ⊆ U)
    (hinv : ∀ p ∈ U, (Ω p.1 p.2).IsInvertible)
    (hskew : ∀ p ∈ U, ∀ v w, Ω p.1 p.2 v w = -Ω p.1 p.2 w v)
    (hclosed : ∀ t b y, y ∈ (extChartAt 𝓘(ℝ, E) b).target →
      (t, (extChartAt 𝓘(ℝ, E) b).symm y) ∈ U → ∀ u v w,
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) b q.2) (t, y) (0, u) v w -
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) b q.2) (t, y) (0, v) u w +
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) b q.2) (t, y) (0, w) u v = 0)
    (htime : ∀ t b y, y ∈ (extChartAt 𝓘(ℝ, E) b).target →
      (t, (extChartAt 𝓘(ℝ, E) b).symm y) ∈ U → ∀ v w,
      fderiv ℝ (fun q : ℝ × E => chartTwoForm (Ω q.1) b q.2) (t, y) (1, 0) v w =
      fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) b q.2) (t, y) (0, v) w -
      fderiv ℝ (fun q : ℝ × E => chartOneForm (α q.1) b q.2) (t, y) (0, w) v)
    (Z : ι → M → E)
    (hface : ∀ i p, p ∈ U → a i < μ i p.2 →
      α p.1 p.2 = 0 ∨
      (Ω p.1 p.2 (Z i p.2) = -mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (μ i) p.2 ∧
        α p.1 p.2 (Z i p.2) = 0))
    {χ : ℝ × M → ℝ} (hχs : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ χ)
    (hχU : tsupport χ ⊆ U)
    (hχ1 : ∀ᶠ p in 𝓝ˢ (Icc (0 : ℝ) 1 ×ˢ {x | ∀ i, μ i x ≤ c i}), χ p = 1)
    (hχC : ∃ C : Set M, IsCompact C ∧ ∀ t x, x ∉ C → χ (t, x) = 0 ∨ α t x = 0) :
    diffeoOf (E := E) (fieldFlow (cutField χ Ω α) 1) '' {x | ∀ i, μ i x ≤ c i} =
        {x | ∀ i, μ i x ≤ c i} ∧
      diffeoOf (E := E) (fieldFlow (cutField χ Ω α) 1) '' interior {x | ∀ i, μ i x ≤ c i} =
        interior {x | ∀ i, μ i x ≤ c i} ∧
      PreservesTwoFormOn (diffeoOf (E := E) (fieldFlow (cutField χ Ω α) 1)) (Ω 0) (Ω 1)
        {x | ∀ i, μ i x ≤ c i} ∧
      (∀ x, (∀ t, α t x = 0) → diffeoOf (E := E) (fieldFlow (cutField χ Ω α) 1) x = x) := by
  apply matchedMoser_spec hΩ hα μ hμ a c hac hU hDU hinv hskew hclosed htime
    Z hface hχs hχU ?_ hχC
  filter_upwards [hχ1] with p hp
  rw [hp,one_smul]

/-- Exact-path form of `cutMoser_spec` (the library's `manifold_exact_sublevel_moser`): the
path of forms is `dΓ_t`, the Moser one-form is `∂_t Γ_t`. -/
theorem cutExactMoser_spec [FiniteDimensional ℝ E] [T2Space M] [IsManifold 𝓘(ℝ, E) ∞ M]
    {Γ : ℝ → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {ι : Type*} (μ : ι → M → ℝ)
    (hμ : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i, a i < c i)
    {U : Set (ℝ × M)} (hU : IsOpen U)
    (hDU : Icc (0 : ℝ) 1 ×ˢ {x | ∀ i, μ i x ≤ c i} ⊆ U)
    (hinv : ∀ p ∈ U, (manifoldExteriorOneForm (Γ p.1) p.2).IsInvertible)
    (Z : ι → M → E)
    (hface : ∀ i p, p ∈ U → a i < μ i p.2 →
      (∀ t, Γ t p.2 = Γ 0 p.2) ∨
      (manifoldExteriorOneForm (Γ p.1) p.2 (Z i p.2) = -mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (μ i) p.2 ∧
        ∀ t, Γ t p.2 (Z i p.2) = Γ 0 p.2 (Z i p.2)))
    {χ : ℝ × M → ℝ} (hχs : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞ χ)
    (hχU : tsupport χ ⊆ U)
    (hχ1 : ∀ᶠ p in 𝓝ˢ (Icc (0 : ℝ) 1 ×ˢ {x | ∀ i, μ i x ≤ c i}), χ p = 1)
    (hχC : ∃ C : Set M, IsCompact C ∧ ∀ t x, x ∉ C → χ (t, x) = 0 ∨ ∀ s, Γ s x = Γ 0 x) :
    let e := diffeoOf (E := E) (fieldFlow (cutField χ (fun s => manifoldExteriorOneForm (Γ s))
      (manifoldTimePrimitive Γ)) 1)
    e '' {x | ∀ i, μ i x ≤ c i} = {x | ∀ i, μ i x ≤ c i} ∧
      e '' interior {x | ∀ i, μ i x ≤ c i} = interior {x | ∀ i, μ i x ≤ c i} ∧
      PreservesTwoFormOn e (manifoldExteriorOneForm (Γ 0)) (manifoldExteriorOneForm (Γ 1))
        {x | ∀ i, μ i x ≤ c i} ∧
      (∀ x, (∀ t, Γ t x = Γ 0 x) → e x = x) := by
  intro e
  have hf : ∀ i p, p ∈ U → a i < μ i p.2 →
      manifoldTimePrimitive Γ p.1 p.2 = 0 ∨
      (manifoldExteriorOneForm (Γ p.1) p.2 (Z i p.2) = -mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (μ i) p.2 ∧
        manifoldTimePrimitive Γ p.1 p.2 (Z i p.2) = 0) := by
    intro i p hp ha
    rcases hface i p hp ha with hz | ⟨hm, hz⟩
    · exact Or.inl (manifoldTimePrimitive_stationary hz p.1)
    · exact Or.inr ⟨hm, manifoldTimePrimitive_eval_constant hΓ hz p.1⟩
  have hΩ := manifoldExteriorOneForm_path_smooth hΓ
  have hα := manifoldTimePrimitive_smooth hΓ
  have hc := manifoldExteriorOneForm_path_closed hΓ
  have ht := manifoldExteriorOneForm_path_time hΓ
  obtain ⟨C, hC, hχC⟩ := hχC
  obtain ⟨hD, hI, hp, hfix⟩ := cutMoser_spec
    (Ω := fun s => manifoldExteriorOneForm (Γ s)) (α := manifoldTimePrimitive Γ)
    hΩ hα μ hμ a c hac hU hDU hinv
    (fun p _ v w => manifoldExteriorOneForm_skew (Γ p.1) p.2 v w)
    (fun t b y hy _ u v w => hc t b y hy u v w)
    (fun t b y hy _ v w => ht t b y hy v w) Z hf hχs hχU hχ1
    ⟨C, hC, fun t x hx => (hχC t x hx).imp_right
      (fun h => manifoldTimePrimitive_stationary h t)⟩
  refine ⟨hD, hI, hp, ?_⟩
  intro x hx
  exact hfix x (fun s => manifoldTimePrimitive_stationary hx s)

end generic

section horizontal

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {M : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The path of product primitives `θ + Γ(t, ·)` on `M × V`. -/
def horizontalPath (Ω : V →L[ℝ] V →L[ℝ] ℝ) (Γ : ℝ × V → ManifoldOneForm E M) (t : ℝ) :
    ManifoldOneForm (E × V) (M × V) :=
  productCouplingPrimitive Ω (fun v => Γ (t, v))

/-- The explicit horizontal relative Moser map with cutoff `χ`. -/
def horizontalMoserMap (Ω : V →L[ℝ] V →L[ℝ] ℝ) (Γ : ℝ × V → ManifoldOneForm E M)
    (χ : ℝ × (M × V) → ℝ) : (M × V) ≃ₘ⟮𝓘(ℝ, E × V), 𝓘(ℝ, E × V)⟯ (M × V) :=
  diffeoOf (E := E × V) (fieldFlow (cutField χ
    (fun s => manifoldExteriorOneForm (horizontalPath Ω Γ s))
    (manifoldTimePrimitive (horizontalPath Ω Γ))) 1)

/-- Explicit form of the library's `horizontal_compact_moser` / `horizontal_moser_endpoint`. -/
theorem horizontalMoserMap_spec
    {Ω : V →L[ℝ] V →L[ℝ] ℝ} (hΩ : Ω.IsInvertible) (hs : ∀ u v, Ω u v = -Ω v u)
    {Γ : ℝ × V → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {D S : Set M} (hS : IsCompact S) (hSD : S ⊆ interior D)
    (hstation : ∀ x, x ∉ S → ∀ t v, Γ (t, v) x = Γ (0, v) x)
    {ι : Type*} (μ : ι → V → ℝ) (hμ : ∀ i, ContDiff ℝ ∞ (μ i))
    (a c : ι → ℝ) (hac : ∀ i, a i < c i)
    (hY : IsCompact {v | ∀ i, μ i v ≤ c i})
    (hInv : ∀ i t x, CollarInvariant Ω (μ i) (a i) (fun v => Γ (t, v) x))
    (hnon : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ D ×ˢ {v | ∀ i, μ i v ≤ c i},
      (globalHorizontalCoupling Ω (fun v => Γ (t, v)) z).IsInvertible)
    {χ : ℝ × (M × V) → ℝ} (hχs : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E × V)) 𝓘(ℝ, ℝ) ∞ χ)
    (hχU : tsupport χ ⊆
      {p | (manifoldExteriorOneForm (horizontalPath Ω Γ p.1) p.2).IsInvertible})
    (hχ1 : ∀ᶠ p in 𝓝ˢ (Icc (0 : ℝ) 1 ×ˢ (D ×ˢ {v | ∀ i, μ i v ≤ c i})), χ p = 1)
    (hχK : ∃ K : Set V, IsCompact K ∧ ∀ t z, z.2 ∉ K → χ (t, z) = 0) :
    horizontalMoserMap Ω Γ χ '' (D ×ˢ {v | ∀ i, μ i v ≤ c i}) =
        D ×ˢ {v | ∀ i, μ i v ≤ c i} ∧
      horizontalMoserMap Ω Γ χ '' interior (D ×ˢ {v | ∀ i, μ i v ≤ c i}) =
        interior (D ×ˢ {v | ∀ i, μ i v ≤ c i}) ∧
      PreservesTwoFormOn (horizontalMoserMap Ω Γ χ)
        (globalHorizontalCoupling Ω (fun v => Γ (0, v)))
        (globalHorizontalCoupling Ω (fun v => Γ (1, v))) (D ×ˢ {v | ∀ i, μ i v ≤ c i}) ∧
      (∀ z, z.1 ∉ S → horizontalMoserMap Ω Γ χ z = z) := by
  obtain ⟨χb, hχb, hCb, hCbD, hχb1⟩ := exists_base_moser_cutoff (E := E) hS hSD
  let Y : Set V := {v | ∀ i, μ i v ≤ c i}
  let Cb : Set M := {x | (1 / 2 : ℝ) ≤ χb x}
  have hSCb : S ⊆ Cb := by
    intro x hx
    change (1 / 2 : ℝ) ≤ χb x
    rw [hχb1 x hx]
    norm_num
  have hsmall : ∀ x, χb x < 3 / 4 → ∀ t v, Γ (t, v) x = Γ (0, v) x := by
    intro x hx t v
    apply hstation x
    intro hs'
    rw [hχb1 x hs'] at hx
    norm_num at hx
  let Λ : ℝ → ManifoldOneForm (E × V) (M × V) := horizontalPath Ω Γ
  have hΛ : SmoothOneFormFamily Λ := productCouplingPrimitive_smooth Ω hΓ
  have hΛe : ∀ t z, manifoldExteriorOneForm (Λ t) z =
      globalHorizontalCoupling Ω (fun v => Γ (t, v)) z := by
    intro t z
    exact productCouplingPrimitive_exterior Ω hs
      (hΓ.comp (contDiff_const.prodMk (contDiff_id : ContDiff ℝ ∞ (fun v : V => v)))) z
  let U := {p : ℝ × (M × V) | (manifoldExteriorOneForm (Λ p.1) p.2).IsInvertible}
  have hU : IsOpen U := manifoldTwoForm_isOpen_nondegenerate
    (Ω := fun s => manifoldExteriorOneForm (Λ s)) (manifoldExteriorOneForm_path_smooth hΛ)
  have hdom := baseFiber_domain χb μ c
  have hCU : Icc (0 : ℝ) 1 ×ˢ {z | ∀ i, baseFiberMoment χb μ i z ≤ baseFiberOuter c i} ⊆ U := by
    intro p hp
    rw [hdom] at hp
    change (manifoldExteriorOneForm (Λ p.1) p.2).IsInvertible
    rw [hΛe]
    exact hnon p.1 hp.1 p.2 ⟨hCbD hp.2.1, hp.2.2⟩
  have hstat : ∀ z : M × V, z.1 ∉ S → ∀ t, Λ t z = Λ 0 z := by
    intro z hz t
    exact productCouplingPrimitive_stationary Ω Γ z (fun s => hstation z.1 hz s z.2) t
  obtain ⟨K, hK, hχK⟩ := hχK
  have hχ1' : ∀ᶠ p in 𝓝ˢ (Icc (0 : ℝ) 1 ×ˢ
      {z | ∀ i, baseFiberMoment χb μ i z ≤ baseFiberOuter c i}), χ p = 1 := by
    apply hχ1.filter_mono (nhdsSet_mono _)
    rw [hdom]
    exact prod_mono le_rfl (prod_mono hCbD le_rfl)
  obtain ⟨hD₁, hI₁, hp₁, hfix₁⟩ := cutExactMoser_spec (E := E × V) (M := M × V)
    hΛ (baseFiberMoment χb μ) (baseFiberMoment_smooth hχb hμ)
    (baseFiberInner a) (baseFiberOuter c) (baseFiber_bounds hac) hU hCU (fun _ hp => hp)
    (baseFiberField Ω μ)
    (fun i p _ hp => productCouplingPrimitive_baseFiber_face hΩ hs hΓ hsmall μ hμ a hInv i p hp)
    hχs hχU hχ1'
    ⟨S ×ˢ K, hS.prod hK, fun t z hz => by
      by_cases h1 : z.1 ∈ S
      · exact Or.inl (hχK t z (fun h2 => hz ⟨h1, h2⟩))
      · exact Or.inr (hstat z h1)⟩
  set e := horizontalMoserMap Ω Γ χ with he_def
  rw [hdom] at hD₁ hI₁ hp₁
  have hfix : ∀ z : M × V, z.1 ∉ S → e z = z := fun z hz => hfix₁ z (hstat z hz)
  have hpD : e '' (D ×ˢ Y) = D ×ˢ Y :=
    image_eq_of_fixed_complement (prod_mono hCbD Subset.rfl) hD₁ (by
      intro z hz hzc
      apply hfix z
      intro hs'
      exact hzc ⟨hSCb hs', hz.2⟩)
  refine ⟨hpD, ?_, ?_, hfix⟩
  · have h := e.toHomeomorph.image_interior (D ×ˢ Y)
    change e '' interior (D ×ˢ Y) = interior (e '' (D ×ˢ Y)) at h
    rw [h, hpD]
  · intro z hz u w
    by_cases hc : z ∈ Cb ×ˢ Y
    · have h := hp₁ z hc u w
      rw [hΛe, hΛe] at h
      exact h
    · have hn : z.1 ∉ S := fun hs' => hc ⟨hSCb hs', hz.2⟩
      have hnh : ∀ᶠ y : M × V in 𝓝 z, y.1 ∉ S :=
        continuousAt_fst.eventually (hS.isClosed.isOpen_compl.mem_nhds hn)
      have hid : (e : M × V → M × V) =ᶠ[𝓝 z] id := hnh.mono (fun y hy => hfix y hy)
      have hd : mfderiv 𝓘(ℝ, E × V) 𝓘(ℝ, E × V) e z =
          mfderiv 𝓘(ℝ, E × V) 𝓘(ℝ, E × V) id z := hid.mfderiv_eq
      have hg : Λ 1 =ᶠ[𝓝 z] Λ 0 := hnh.mono (fun y hy => hstat y hy 1)
      have hx := manifoldExteriorOneForm_congr_germ hg
      rw [hd, mfderiv_id]
      change globalHorizontalCoupling Ω (fun v => Γ (1, v)) (e z) u w =
        globalHorizontalCoupling Ω (fun v => Γ (0, v)) z u w
      rw [hfix z hn, ← hΛe, ← hΛe, hx]

end horizontal

section toric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M] [IsManifold 𝓘(ℝ, Plane) ∞ M]
  [T2Space M] [NormalSpace M] [SigmaCompactSpace M]

/-- The interpolating family `Γ(t, v) = ((1 − t)Γ₀ + tΓ₁)(planeMoments v)`. -/
def toricInterp (Γ₀ Γ₁ : (ι → ℝ) → ManifoldOneForm Plane M) (q : ℝ × PlanePhase ι) :
    ManifoldOneForm Plane M :=
  toricPrimitiveInterpolation Γ₀ Γ₁ (q.1, planeMoments q.2)

/-- **The explicit toric relative Moser map** with cutoff `χ`: the time-one map of the
cut-off Moser field of the linear path of primitives from `Γ₀` to `Γ₁`. -/
def toricMoserMap (Γ₀ Γ₁ : (ι → ℝ) → ManifoldOneForm Plane M)
    (χ : ℝ × (M × PlanePhase ι) → ℝ) :
    (M × PlanePhase ι) ≃ₘ⟮𝓘(ℝ, Plane × PlanePhase ι), 𝓘(ℝ, Plane × PlanePhase ι)⟯
      (M × PlanePhase ι) :=
  horizontalMoserMap phaseArea (toricInterp Γ₀ Γ₁) χ

/-- Explicit form of the library's `toric_redistribution_moser`. -/
theorem toricMoserMap_spec
    {Γ₀ Γ₁ : (ι → ℝ) → ManifoldOneForm Plane M}
    (h₀ : SmoothOneFormFamily Γ₀) (h₁ : SmoothOneFormFamily Γ₁)
    {D S : Set M} (hS : IsCompact S) (hSD : S ⊆ interior D)
    (hstation : ∀ x, x ∉ S → ∀ p, Γ₁ p x = Γ₀ p x)
    {Y : Set (ι → ℝ)}
    (hp₀ : ∀ p ∈ Y, ∀ x ∈ D, 0 < chartTwoForm (manifoldExteriorOneForm (Γ₀ p))
      x (extChartAt 𝓘(ℝ, Plane) x x) (1, 0) (0, 1))
    (hp₁ : ∀ p ∈ Y, ∀ x ∈ D, 0 < chartTwoForm (manifoldExteriorOneForm (Γ₁ p))
      x (extChartAt 𝓘(ℝ, Plane) x x) (1, 0) (0, 1))
    {J : Type*} (F : J → (ι → ℝ) → ℝ) (hF : ∀ j, ContDiff ℝ ∞ (F j))
    (α c : J → ℝ) (hαc : ∀ j, α j < c j)
    (hYeq : planeMoments ⁻¹' Y = {v | ∀ j, (F j ∘ planeMoments) v ≤ c j})
    (hYC : IsCompact (planeMoments ⁻¹' Y))
    {χ : ℝ × (M × PlanePhase ι) → ℝ}
    (hχs : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Plane × PlanePhase ι)) 𝓘(ℝ, ℝ) ∞ χ)
    (hχU : tsupport χ ⊆ {p | (manifoldExteriorOneForm
      (horizontalPath phaseArea (toricInterp Γ₀ Γ₁) p.1) p.2).IsInvertible})
    (hχ1 : ∀ᶠ p in 𝓝ˢ (Icc (0 : ℝ) 1 ×ˢ (D ×ˢ (planeMoments ⁻¹' Y))), χ p = 1)
    (hχK : ∃ K : Set (PlanePhase ι), IsCompact K ∧ ∀ t z, z.2 ∉ K → χ (t, z) = 0) :
    toricMoserMap Γ₀ Γ₁ χ '' (D ×ˢ (planeMoments ⁻¹' Y)) = D ×ˢ (planeMoments ⁻¹' Y) ∧
      toricMoserMap Γ₀ Γ₁ χ '' interior (D ×ˢ (planeMoments ⁻¹' Y)) =
        interior (D ×ˢ (planeMoments ⁻¹' Y)) ∧
      PreservesTwoFormOn (toricMoserMap Γ₀ Γ₁ χ)
        (globalHorizontalCoupling phaseArea (Γ₀ ∘ planeMoments))
        (globalHorizontalCoupling phaseArea (Γ₁ ∘ planeMoments)) (D ×ˢ (planeMoments ⁻¹' Y)) ∧
      (∀ z, z.1 ∉ S → toricMoserMap Γ₀ Γ₁ χ z = z) := by
  have hdom : {v | ∀ j, F j (planeMoments v) ≤ c j} = planeMoments ⁻¹' Y := hYeq.symm
  have hsmooth := toricPrimitiveInterpolation_smooth h₀ h₁
  have hparam : ∀ t x, ContDiff ℝ ∞ (fun p => toricPrimitiveInterpolation Γ₀ Γ₁ (t, p) x) := by
    intro t x
    exact (contDiff_iff_contDiffAt.mpr (fun q => hsmooth.parameter_contDiffAt q x)).comp
      (contDiff_const.prodMk contDiff_id)
  have hΓ : SmoothOneFormFamily (toricInterp Γ₀ Γ₁) :=
    hsmooth.comp (contDiff_fst.prodMk (planeMoments_smooth.comp contDiff_snd))
  have h := horizontalMoserMap_spec phaseArea_isInvertible phaseArea_skew hΓ hS hSD
    (fun x hx t v => by
      simp only [toricInterp, toricPrimitiveInterpolation, Pi.add_apply, Pi.smul_apply,
        hstation x hx, ← add_smul]
      congr 1; ring)
    (fun j => F j ∘ planeMoments) (fun j => (hF j).comp planeMoments_smooth)
    α c hαc (hYeq ▸ hYC)
    (fun j t x => toric_collarInvariant (hF j) (hparam t x) (α j))
    (fun t ht z hz => toricPrimitiveInterpolation_isInvertible h₀ h₁ ht z
      (hp₀ _ (by exact (show z.2 ∈ planeMoments ⁻¹' Y from hYeq.symm ▸ hz.2)) _ hz.1)
      (hp₁ _ (by exact (show z.2 ∈ planeMoments ⁻¹' Y from hYeq.symm ▸ hz.2)) _ hz.1))
    hχs hχU (by simpa only [← hYeq] using hχ1) hχK
  obtain ⟨hD, hI, hp, hfix⟩ := h
  refine ⟨?_, ?_, ?_, hfix⟩
  · rw [← hYeq] at hD
    exact hD
  · rw [← hYeq] at hI
    exact hI
  · simp only [toricInterp, toricPrimitiveInterpolation_zero,
      toricPrimitiveInterpolation_one] at hp
    rw [hYeq]
    convert hp using 1 <;> rfl

end toric

section model

open OAI.PackingSufficiencySupport.MomentPolytope (Moments region planeRegion)

variable {M : Type} [TopologicalSpace M] [ChartedSpace (ℝ × ℝ) M]
  [IsManifold 𝓘(ℝ, ℝ × ℝ) ∞ M] [T2Space M] [_root_.NormalSpace M] [SigmaCompactSpace M]
variable {m q : ℕ}

/-- Standing hypotheses on the target primitive `Γ₁` (those `exists_surface_step_two`
provides for the normalized primitive): a smooth family, equal to `T.Γ` off a compact subset
of `int base`, with `dΓ₁(p) = κ₁(p, ·) Λ` for a smooth `κ₁` positive on `Δ × base`. -/
structure TargetPrimitive (T : ToricModel M m q) (Γ₁ : Moments m → ManifoldOneForm Plane M) :
    Prop where
  smooth : SmoothOneFormFamily Γ₁
  station : ∃ S : Set M, IsCompact S ∧ S ⊆ interior T.base ∧ ∀ x, x ∉ S → ∀ p, Γ₁ p x = T.Γ p x
  curv : ∃ κ : Moments m × M → ℝ,
    ContMDiff (𝓘(ℝ, Moments m).prod 𝓘(ℝ, ℝ × ℝ)) 𝓘(ℝ, ℝ) ∞ κ ∧
    (∀ p x, manifoldExteriorOneForm (Γ₁ p) x = κ (p, x) • T.Λ x) ∧
    ∀ p ∈ T.Δ.set, ∀ x ∈ T.base, 0 < κ (p, x)

theorem region_compact {T : ToricModel M m q} (hT : T.Spec) : IsCompact T.region :=
  hT.base_compact.prod (isCompact_preimage_planeMoments hT.Δ_spec.compact)

/-- Positivity of the model primitive's base coefficient on `Δ × base`. -/
theorem model_pos {T : ToricModel M m q} (hT : T.Spec) :
    ∀ p ∈ T.Δ.set, ∀ x ∈ T.base, 0 < chartTwoForm (manifoldExteriorOneForm (T.Γ p))
      x (extChartAt 𝓘(ℝ, Plane) x x) (1, 0) (0, 1) := by
  intro p hp x hx
  have heq : manifoldExteriorOneForm (T.Γ p) = fun x => T.dens (p, x) • T.Λ x :=
    funext (hT.dΓ p)
  rw [heq, chartTwoForm_spatial_smul]
  change 0 < T.dens (p, (extChartAt 𝓘(ℝ, Plane) x).symm (extChartAt 𝓘(ℝ, Plane) x x)) *
    chartTwoForm T.Λ x (extChartAt 𝓘(ℝ, Plane) x x) (1, 0) (0, 1)
  simpa using mul_pos (hT.dens_pos p hp x hx) (hT.Λ_pos x _ (mem_extChartAt_target x))

/-- Positivity of the target primitive's base coefficient on `Δ × base`. -/
theorem target_pos {T : ToricModel M m q} (hT : T.Spec)
    {Γ₁ : Moments m → ManifoldOneForm Plane M} (h₁ : TargetPrimitive T Γ₁) :
    ∀ p ∈ T.Δ.set, ∀ x ∈ T.base, 0 < chartTwoForm (manifoldExteriorOneForm (Γ₁ p))
      x (extChartAt 𝓘(ℝ, Plane) x x) (1, 0) (0, 1) := by
  obtain ⟨κ, -, hκ, hκp⟩ := h₁.curv
  intro p hp x hx
  have heq : manifoldExteriorOneForm (Γ₁ p) = fun x => κ (p, x) • T.Λ x := funext (hκ p)
  rw [heq, chartTwoForm_spatial_smul]
  change 0 < κ (p, (extChartAt 𝓘(ℝ, Plane) x).symm (extChartAt 𝓘(ℝ, Plane) x x)) *
    chartTwoForm T.Λ x (extChartAt 𝓘(ℝ, Plane) x x) (1, 0) (0, 1)
  simpa using mul_pos (hκp p hp x hx) (hT.Λ_pos x _ (mem_extChartAt_target x))

end model

end SymplecticPacking.HighDim.ToricPackingStages
