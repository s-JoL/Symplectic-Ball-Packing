import SymplecticPacking.BranchLarge3.OAIOpen
import SymplecticPacking.Explicit

/-!
# Local exact Moser transport

`Line` and `Good` express a compact flow enclosure at a supplied positive time.
`spec_at` proves local embedding and pullback identities from that enclosure.
The unique uncut-flow endpoint is used in comparison proofs; the cubic construction
uses the native finite-chart flow and compact derivative stopping rule in
`CubicTransferTime` and `CubicTransferMap`.
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3.ExactCore

open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set

section defs

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

/-- The (uncut) Moser field: the unique `v` with `dΓ_t(x) v = -∂_tΓ_t(x)`. -/
def mfield (Γ : ℝ → ManifoldOneForm E M) (p : ℝ × M) : E :=
  open Classical in
  if h : ∃! v : E, manifoldExteriorOneForm (Γ p.1) p.2 v = -manifoldTimePrimitive Γ p.1 p.2
  then Explicit.the h else 0

/-- The admissible region. -/
def region (Γ : ℝ → ManifoldOneForm E M) (U : Set M) (A : ℝ × M → N) (T : Set N) :
    Set (ℝ × M) :=
  {p | (manifoldExteriorOneForm (Γ p.1) p.2).IsInvertible ∧ p.2 ∈ U ∧ A p ∈ T}

/-- A flow line from `x` on `(-ε, a + ε)` with graph in `S`. -/
def Line (Γ : ℝ → ManifoldOneForm E M) (S : Set (ℝ × M)) (ε a : ℝ) (x : M) (γ : ℝ → M) :
    Prop :=
  γ 0 = x ∧ ∀ r ∈ Ioo (-ε) (a + ε), (r, γ r) ∈ S ∧
    HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ r
      (((1 : ℝ →L[ℝ] ℝ).smulRight (mfield Γ (r, γ r)) : ℝ →L[ℝ] E))

/-- `y` is the time-`s` endpoint of a flow line from `x` inside the region. -/
def Reach (Γ : ℝ → ManifoldOneForm E M) (U : Set M) (A : ℝ × M → N) (T : Set N)
    (s : ℝ) (x y : M) : Prop :=
  ∃ ε > 0, ∃ γ : ℝ → M, Line Γ (region Γ U A T) ε s x γ ∧ γ s = y

/-- The explicit Moser flow: the unique endpoint (definite description). -/
def flow (Γ : ℝ → ManifoldOneForm E M) (U : Set M) (A : ℝ × M → N) (T : Set N)
    (s : ℝ) (x : M) : M :=
  open Classical in
  if h : ∃! y, Reach Γ U A T s x y then Explicit.the h else x

/-- Admissible times. -/
def Good (Γ : ℝ → ManifoldOneForm E M) (K U : Set M) (δ : ℝ) (A : ℝ × M → N) (T : Set N)
    (a : ℝ) : Prop :=
  a ∈ Icc 0 (min δ 1) ∧ ∃ C : Set (ℝ × M), IsCompact C ∧ C ⊆ region Γ U A T ∧
    ∃ ε > 0, ε ≤ 1 / 2 ∧ ∀ x ∈ K, ∃ γ, Line Γ C ε a x γ

/-- The explicit transfer map at time `t`. -/
def map (Γ : ℝ → ManifoldOneForm E M) (U : Set M) (A : ℝ × M → N) (T : Set N) (t : ℝ)
    (x : M) : N :=
  A (t, flow Γ U A T t x)

end defs

section proofs

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M N : Type*} [TopologicalSpace M] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N]

omit [FiniteDimensional ℝ E] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem mfield_eq {Γ : ℝ → ManifoldOneForm E M} {p : ℝ × M}
    (h : (manifoldExteriorOneForm (Γ p.1) p.2).IsInvertible) :
    mfield Γ p = manifoldMoserField (fun t => manifoldExteriorOneForm (Γ t))
      (manifoldTimePrimitive Γ) p := by
  obtain ⟨e, he⟩ := h
  set B := manifoldExteriorOneForm (Γ p.1) p.2 with hB
  have hv : B (-B.inverse (manifoldTimePrimitive Γ p.1 p.2)) =
      -manifoldTimePrimitive Γ p.1 p.2 := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
    simp
  have hu : ∃! v : E, B v = -manifoldTimePrimitive Γ p.1 p.2 := by
    refine ⟨_, hv, fun y hy => ?_⟩
    have h2 := hy.trans hv.symm
    rw [← he] at h2
    have h3 := e.injective h2
    rw [he] at h3
    exact h3
  unfold mfield
  rw [dite_eq_left_of_eq_true (eq_true hu)]
  exact Explicit.the_eq hu hv

omit [T2Space M] [NormalSpace M] [SigmaCompactSpace M] in
theorem region_isOpen {Γ : ℝ → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {U : Set M} (hU : IsOpen U) {A : ℝ × M → N} (hA : Continuous A) {T : Set N}
    (hT : IsOpen T) : IsOpen (region Γ U A T) := by
  have h1 : IsOpen {p : ℝ × M | (manifoldExteriorOneForm (Γ p.1) p.2).IsInvertible} :=
    manifoldTwoForm_isOpen_nondegenerate (Ω := fun t => manifoldExteriorOneForm (Γ t))
      (manifoldExteriorOneForm_path_smooth hΓ)
  exact h1.inter ((hU.preimage continuous_snd).inter (hT.preimage hA))

/-- A localized Moser field around a compact subset of the region, and its flow. -/
theorem local_flow {Γ : ℝ → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {C R : Set (ℝ × M)} (hC : IsCompact C) (hR : IsOpen R) (hCR : C ⊆ R)
    (hinv : ∀ p ∈ R, (manifoldExteriorOneForm (Γ p.1) p.2).IsInvertible) :
    ∃ V : (p : ℝ × M) → TangentSpace 𝓘(ℝ, E) p.2,
      ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞
        (fun p => (⟨p.2, V p⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      ∃ O : Set (ℝ × M), IsOpen O ∧ C ⊆ O ∧ O ⊆ R ∧ (∀ p ∈ O, V p = mfield Γ p) ∧
      (∀ p ∈ O, V p = manifoldMoserField (fun t => manifoldExteriorOneForm (Γ t))
        (manifoldTimePrimitive Γ) p) ∧
      ∃ Φ Ψ : ℝ × M → M,
        ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ Φ ∧
        ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ Ψ ∧
        (∀ x, Φ (0, x) = x) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ x, Ψ (t, Φ (t, x)) = x ∧ Φ (t, Ψ (t, x)) = x) ∧
        (∀ x t, t ∈ Ioo (-2 : ℝ) 2 → HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
          (fun s => Φ (s, x)) t ((1 : ℝ →L[ℝ] ℝ).smulRight (V (t, Φ (t, x))))) := by
  have hΩ : SmoothTwoFormFamily (fun t => manifoldExteriorOneForm (Γ t)) :=
    manifoldExteriorOneForm_path_smooth hΓ
  have hα : SmoothOneFormFamily (manifoldTimePrimitive Γ) := manifoldTimePrimitive_smooth hΓ
  obtain ⟨V, hV, hVe, _hVz, ⟨K', hK', hVK'⟩, _hVL⟩ :=
    exists_joint_localized_manifold_moser_field (Ω := fun t => manifoldExteriorOneForm (Γ t))
      (α := manifoldTimePrimitive Γ) hΩ hα hC hR hCR hinv
  obtain ⟨O, hO, hCO, hOV⟩ := mem_nhdsSet_iff_exists.mp hVe
  obtain ⟨Φ, Ψ, hΦ, hΨ, hΦ0, hΦi, hODE, _⟩ :=
    exists_spatially_compact_nonautonomous_flow hV hK' hVK'
  refine ⟨V, hV, O ∩ R, hO.inter hR, fun p hp => ⟨hCO hp, hCR hp⟩, inter_subset_right,
    fun p hp => ?_, fun p hp => hOV hp.1, Φ, Ψ, hΦ, hΨ, hΦ0, hΦi, hODE⟩
  rw [mfield_eq (hinv p hp.2)]
  exact hOV hp.1

omit [FiniteDimensional ℝ E] [T2Space M] [NormalSpace M] [SigmaCompactSpace M]
  [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem Line.continuousOn {Γ : ℝ → ManifoldOneForm E M} {S : Set (ℝ × M)} {ε a : ℝ} {x : M}
    {γ : ℝ → M} (h : Line Γ S ε a x γ) : ContinuousOn γ (Ioo (-ε) (a + ε)) :=
  fun r hr => ((h.2 r hr).2.continuousAt).continuousWithinAt

/-- Uniqueness of flow-line endpoints inside the region. -/
theorem line_endpoint_unique {Γ : ℝ → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {U : Set M} (hU : IsOpen U) {A : ℝ × M → N} (hA : Continuous A) {T : Set N}
    (hT : IsOpen T) {s : ℝ} (hs : 0 ≤ s) {x : M} {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    {γ₁ γ₂ : ℝ → M} (h₁ : Line Γ (region Γ U A T) ε₁ s x γ₁)
    (h₂ : Line Γ (region Γ U A T) ε₂ s x γ₂) : γ₁ s = γ₂ s := by
  set e := min ε₁ ε₂ / 2 with he
  have he0 : 0 < e := by positivity
  have he1 : e < ε₁ := by have := min_le_left ε₁ ε₂; linarith
  have he2 : e < ε₂ := by have := min_le_right ε₁ ε₂; linarith
  have hsub₁ : Icc (-e) (s + e) ⊆ Ioo (-ε₁) (s + ε₁) := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  have hsub₂ : Icc (-e) (s + e) ⊆ Ioo (-ε₂) (s + ε₂) := fun r hr =>
    ⟨by linarith [hr.1], by linarith [hr.2]⟩
  let G₁ : ℝ → ℝ × M := fun r => (r, γ₁ r)
  let G₂ : ℝ → ℝ × M := fun r => (r, γ₂ r)
  have hc₁ : IsCompact (G₁ '' Icc (-e) (s + e)) :=
    isCompact_Icc.image_of_continuousOn
      (continuousOn_id.prodMk (h₁.continuousOn.mono hsub₁))
  have hc₂ : IsCompact (G₂ '' Icc (-e) (s + e)) :=
    isCompact_Icc.image_of_continuousOn
      (continuousOn_id.prodMk (h₂.continuousOn.mono hsub₂))
  have hR := region_isOpen hΓ hU hA hT
  have hCR : G₁ '' Icc (-e) (s + e) ∪ G₂ '' Icc (-e) (s + e) ⊆ region Γ U A T := by
    rintro _ (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · exact (h₁.2 r (hsub₁ hr)).1
    · exact (h₂.2 r (hsub₂ hr)).1
  obtain ⟨V, hV, O, _hO, hCO, _hOR, hVO, -, -⟩ :=
    local_flow hΓ (hc₁.union hc₂) hR hCR (fun p hp => hp.1)
  have hIoo : Ioo (-e) (s + e) ⊆ Icc (-e) (s + e) := Ioo_subset_Icc_self
  have heq := nonautonomous_curve_eqOn hV (a := -e) (b := s + e) (t₀ := 0)
    ⟨by linarith, by linarith⟩ (γ := γ₁) (δ := γ₂)
    (fun r hr => by
      have hh := (h₁.2 r (hsub₁ (hIoo hr))).2
      rwa [← hVO _ (hCO (Or.inl ⟨r, hIoo hr, rfl⟩))] at hh)
    (fun r hr => by
      have hh := (h₂.2 r (hsub₂ (hIoo hr))).2
      rwa [← hVO _ (hCO (Or.inr ⟨r, hIoo hr, rfl⟩))] at hh)
    (h₁.1.trans h₂.1.symm)
  exact heq ⟨by linarith, by linarith⟩

theorem flow_eq {Γ : ℝ → ManifoldOneForm E M} (hΓ : SmoothOneFormFamily Γ)
    {U : Set M} (hU : IsOpen U) {A : ℝ × M → N} (hA : Continuous A) {T : Set N}
    (hT : IsOpen T) {s : ℝ} (hs : 0 ≤ s) {x : M} {ε : ℝ} (hε : 0 < ε) {γ : ℝ → M}
    (h : Line Γ (region Γ U A T) ε s x γ) : flow Γ U A T s x = γ s := by
  have hu : ∃! y, Reach Γ U A T s x y := by
    refine ⟨γ s, ⟨ε, hε, γ, h, rfl⟩, ?_⟩
    rintro y ⟨ε', hε', γ', h', rfl⟩
    exact line_endpoint_unique hΓ hU hA hT hs hε' hε h' h
  unfold flow
  rw [dite_eq_left_of_eq_true (eq_true hu)]
  exact Explicit.the_eq hu ⟨ε, hε, γ, h, rfl⟩

/-- The core specification (smoothness on the neighbourhood `W`). -/
theorem spec_at {Γ : ℝ → ManifoldOneForm E M}
    (hΓ : SmoothOneFormFamily Γ) {K : Set M} (hK : IsCompact K)
    (hinv : ∀ x ∈ K, (manifoldExteriorOneForm (Γ 0) x).IsInvertible)
    {U : Set M} (hU : IsOpen U) (hKU : K ⊆ U)
    {δ : ℝ} (hδ : 0 < δ) {A : ℝ × M → N}
    (hA : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, F) ∞ A)
    (hemb : ∀ t ∈ Ioc (0 : ℝ) δ, Topology.IsEmbedding (fun x : U => A (t, x.val)))
    {T : Set N} (hT : IsOpen T) (hinto : MapsTo (fun x => A (0, x)) K T)
    {t : ℝ} (htpos : 0 < t) (hgood : Good Γ K U δ A T t)
    (Ω : ℝ → ManifoldTwoForm F N)
    (hform : ∀ t ∈ Ioc (0 : ℝ) δ, ∀ x ∈ U,
      manifoldExteriorOneForm (Γ t) x = (Ω t (A (t, x))).bilinearComp
        (manifoldMapDifferential (E := F) (F := E) (fun y => A (t, y)) x)
        (manifoldMapDifferential (E := F) (F := E) (fun y => A (t, y)) x)) :
    let g := map Γ U A T t
    t ∈ Ioc (0 : ℝ) δ ∧ ∃ W : Set M, IsOpen W ∧ K ⊆ W ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g W ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
      MapsTo g W T ∧ ∀ x ∈ W, ∀ v w, Ω t (g x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) g x w) = manifoldExteriorOneForm (Γ 0) x v w := by
  intro g
  obtain ⟨htI, C, hC, hCR, ε, hε, hε2, hl⟩ := hgood
  change t ∈ Icc 0 (min δ 1) at htI
  have htδ : t ≤ δ := htI.2.trans (min_le_left _ _)
  have ht1 : t ≤ 1 := htI.2.trans (min_le_right _ _)
  have hR := region_isOpen hΓ hU hA.continuous hT
  obtain ⟨V, hV, O, hO, hCO, hOR, hVO, hVM, Φ, Ψ, hΦ, hΨ, hΦ0, hΦi, hODE⟩ :=
    local_flow hΓ hC hR hCR (fun p hp => hp.1)
  -- the flow lines from `K` are the lines of `Φ`
  have hagree (x : M) (hx : x ∈ K) (r : ℝ) (hr : r ∈ Ioo (-ε) (t + ε)) :
      (r, Φ (r, x)) ∈ C := by
    obtain ⟨γ, hγ0, hγ⟩ := hl x hx
    have heq := nonautonomous_curve_eqOn hV (a := -ε) (b := t + ε) (t₀ := 0)
      ⟨by linarith, by linarith⟩ (γ := γ) (δ := fun s => Φ (s, x))
      (fun s hs => by
        have hh := (hγ s hs).2
        rwa [← hVO _ (hCO (hγ s hs).1)] at hh)
      (fun s hs => hODE x s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (by rw [hγ0, hΦ0])
    have := (hγ r hr).1
    rwa [heq hr] at this
  let G : ℝ × M → ℝ × M := fun p => (p.1, Φ p)
  have hG : Continuous G := continuous_fst.prodMk hΦ.continuous
  have hsub : Icc (-(ε / 2)) (t + ε / 2) ×ˢ K ⊆ G ⁻¹' O := by
    rintro ⟨r, x⟩ ⟨hr, hx⟩
    exact hCO (hagree x hx r ⟨by linarith [hr.1], by linarith [hr.2]⟩)
  obtain ⟨T1, W, _hT1, hW, hIT, hKW, hTW⟩ :=
    generalized_tube_lemma isCompact_Icc hK (hO.preimage hG) hsub
  have hstay (x : M) (hx : x ∈ W) (r : ℝ) (hr : r ∈ Icc (-(ε / 2)) (t + ε / 2)) :
      (r, Φ (r, x)) ∈ O := hTW (mk_mem_prod (hIT hr) hx)
  -- on `W` the explicit map is the time-`t` map of `Φ`
  have hline (x : M) (hx : x ∈ W) :
      Line Γ (region Γ U A T) (ε / 2) t x (fun s => Φ (s, x)) := by
    refine ⟨hΦ0 x, fun r hr => ?_⟩
    have hrI : r ∈ Icc (-(ε / 2)) (t + ε / 2) := Ioo_subset_Icc_self hr
    refine ⟨hOR (hstay x hx r hrI), ?_⟩
    have hd := hODE x r ⟨by linarith [hr.1], by linarith [hr.2]⟩
    rw [hVO _ (hstay x hx r hrI)] at hd
    exact hd
  have hflow (x : M) (hx : x ∈ W) : flow Γ U A T t x = Φ (t, x) :=
    flow_eq hΓ hU hA.continuous hT htpos.le (by positivity) (hline x hx)
  have htW (x : M) (hx : x ∈ W) : (t, Φ (t, x)) ∈ region Γ U A T :=
    hOR (hstay x hx t ⟨by linarith, by linarith⟩)
  let g' : M → N := fun x => A (t, Φ (t, x))
  have hgg' (x : M) (hx : x ∈ W) : g x = g' x := by
    change A (t, flow Γ U A T t x) = A (t, Φ (t, x))
    rw [hflow x hx]
  have hφ := hΦ.comp (contMDiff_const.prodMk contMDiff_id) (f := fun x : M => (t, x))
  have hψ := hΨ.comp (contMDiff_const.prodMk contMDiff_id) (f := fun x : M => (t, x))
  have ha := hA.comp (contMDiff_const.prodMk contMDiff_id) (f := fun x : M => (t, x))
  have hg' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ g' := ha.comp hφ
  have hφemb : Topology.IsEmbedding (fun x : M => Φ (t, x)) := by
    apply Topology.IsEmbedding.of_comp hφ.continuous hψ.continuous
    have he : (fun x : M => Ψ (t, Φ (t, x))) = id :=
      funext fun x => (hΦi t ⟨htpos.le, ht1⟩ x).1
    change Topology.IsEmbedding (fun x : M => Ψ (t, Φ (t, x)))
    rw [he]
    exact Topology.IsEmbedding.id
  refine ⟨⟨htpos, htδ⟩, W, hW, hKW, ?_, ?_, ?_, ?_⟩
  · exact hg'.contMDiffOn.congr (fun x hx => hgg' x hx)
  · have he : (fun x : W => g x.val) = (fun x : W => g' x.val) :=
      funext fun x => hgg' x.val x.property
    rw [he]
    exact (hemb t ⟨htpos, htδ⟩).comp
      ((hφemb.comp Topology.IsEmbedding.subtypeVal).codRestrict U
        (fun x : W => (htW x.val x.property).2.1))
  · intro x hx
    rw [hgg' x hx]
    exact (htW x hx).2.2
  · intro x hx v w
    have hev : g =ᶠ[𝓝 x] g' := Filter.eventually_of_mem (hW.mem_nhds hx) hgg'
    rw [hev.mfderiv_eq, hgg' x hx]
    -- the pulled-back form is constant along the flow
    have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) (v w : E) :
        HasDerivAt (fun r => manifoldPullback Φ (fun r => manifoldExteriorOneForm (Γ r)) r x v w)
          0 s :=
      exact_path_local_transport_derivative hΓ hΦ hV hODE hO
        (fun p hp => (hOR hp).1) hVM
        (show s ∈ Ioo (-2 : ℝ) 2 by constructor <;> linarith [hs.1, hs.2])
        (hstay x hx s ⟨by linarith [hs.1], by linarith [hs.2]⟩) v w
    have hconst (v w : E) :
        manifoldPullback Φ (fun r => manifoldExteriorOneForm (Γ r)) t x v w =
          manifoldExteriorOneForm (Γ 0) x v w := by
      have he := (convex_Icc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun s hs => (hd s hs v w).hasDerivWithinAt)
        (fun _ _ => (by simp : ‖(0 : ℝ)‖ ≤ (0 : ℝ)))
        (show (0 : ℝ) ∈ Icc (0 : ℝ) t from ⟨le_rfl, htpos.le⟩)
        (show t ∈ Icc (0 : ℝ) t from ⟨htpos.le, le_rfl⟩)
      have he' : manifoldPullback Φ (fun r => manifoldExteriorOneForm (Γ r)) t x v w =
          manifoldPullback Φ (fun r => manifoldExteriorOneForm (Γ r)) 0 x v w := by
        simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using he
      rw [he']
      have hid : (fun y => Φ (0, y)) = id := funext hΦ0
      have hD : preferredDifferential (fun y => Φ (0, y)) x = ContinuousLinearMap.id ℝ E := by
        change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y => Φ (0, y)) x = _
        rw [hid]; exact mfderiv_id
      rw [manifoldPullback, hD]
      simp only [hΦ0, ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.id_apply]
    have hdc := mfderiv_comp x (ha.mdifferentiable (by simp) (Φ (t, x)))
      (hφ.mdifferentiable (by simp) x)
    change Ω t (A (t, Φ (t, x)))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) ((A ∘ fun y => (t, y)) ∘ (Φ ∘ fun y => (t, y))) x v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) ((A ∘ fun y => (t, y)) ∘ (Φ ∘ fun y => (t, y))) x w) = _
    rw [hdc]
    have hf := congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ =>
      B (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y => Φ (t, y)) x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y => Φ (t, y)) x w))
      (hform t ⟨htpos, htδ⟩ (Φ (t, x)) (htW x hx).2.1)
    exact hf.symm.trans (hconst v w)


end proofs

end SymplecticPacking.BranchLarge3.ExactCore
