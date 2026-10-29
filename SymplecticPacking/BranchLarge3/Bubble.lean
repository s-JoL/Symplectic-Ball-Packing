import SymplecticPacking.BranchLarge3.EuclideanGuards

/-!
# Steps S6–S7: the large ball (cubic bubble)

* S6 (explicit, proved): the integer orders `m = ⌊r₀ L⌋`, `p = m + 2`, `N = m + 3` and the lower
  bound `Q = ⌊3/(a - r₀)⌋ + 1` for `L` (OpenAI `exists_bubble_integer_orders`).
* Separation (explicit, proved): the compact image `K' = firstToDistinguished '' K` and the
  origin are separated by the open sets `{Σ|xⱼ|² > ρ²/4}` and `{Σ|xⱼ|² < ρ²/4}`,
  `ρ = infDist 0 K'`.
* S7a: explicit uniform bubble deformation of the outer packing
  (OpenAI `outer_packing_uniform_bubble_into`): an explicit threshold `τ` and, for every
  `ε ∈ (0, τ]`, explicit maps into the bubble form `cubicOuterBubbleForm … ε` staying in `T`.
* S7b: explicit embedding of the large ball into the bubble chart near the origin
  (OpenAI `exists_uniform_cubic_bubble_ball`).

Paper: supplement `six-return.tex` (large ball, bubble); main `thm:lrg-six`.
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3

open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set

/-! ### S6: integer orders -/

/-- Lower bound for the degree: `Q = ⌊3/(a - r₀)⌋ + 1`. -/
def bubbleQ (r₀ a : ℝ) : ℕ := ⌊3 / (a - r₀)⌋₊ + 1

/-- `m = ⌊r₀ L⌋`. -/
def bubbleM (r₀ : ℝ) (L : ℕ) : ℕ := ⌊r₀ * (L : ℝ)⌋₊

theorem bubble_orders_spec {r₀ a : ℝ} (hr : 0 ≤ r₀) (hra : r₀ < a) {L S : ℕ}
    (hQL : bubbleQ r₀ a < L) (hSL : S ≤ L) (hS : (S : ℝ) = (L : ℝ) * (1 - a)) :
    let m := bubbleM r₀ L
    m + 1 < m + 2 ∧ m + 2 < L - S ∧ m + 2 < m + 3 ∧ r₀ < ((m + 1 : ℕ) : ℝ) / (L : ℝ) := by
  intro m
  have hQ : 3 / (a - r₀) < (bubbleQ r₀ a : ℝ) := by
    unfold bubbleQ; push_cast; exact Nat.lt_floor_add_one _
  have hL : 0 < (L : ℝ) := by
    have : 0 < L := lt_of_le_of_lt (Nat.zero_le _) hQL
    exact_mod_cast this
  have hδ : 0 < a - r₀ := sub_pos.mpr hra
  have hgap : 3 < (L : ℝ) * (a - r₀) :=
    (div_lt_iff₀ hδ).mp (hQ.trans (by exact_mod_cast hQL))
  have hmle : (m : ℝ) ≤ r₀ * (L : ℝ) := Nat.floor_le (mul_nonneg hr hL.le)
  have hmlt : r₀ * (L : ℝ) < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  have he : ((L - S : ℕ) : ℝ) = (L : ℝ) * a := by rw [Nat.cast_sub hSL, hS]; ring
  refine ⟨by omega, ?_, by omega, ?_⟩
  · apply (Nat.cast_lt (α := ℝ)).mp
    push_cast
    rw [he]
    nlinarith
  · apply (lt_div_iff₀ hL).mpr
    exact_mod_cast hmlt

/-! ### Separation of the outer image from the origin -/

/-- The separation radius `ρ = infDist 0 K'` (`1` if `K'` is empty). -/
def sepRad (K' : Set (Fin 3 → ℂ)) : ℝ :=
  open Classical in if K'.Nonempty then Metric.infDist 0 K' else 1

/-- The outer side of the Euclidean energy separator. -/
def sepOuter (K' : Set (Fin 3 → ℂ)) : Set (Fin 3 → ℂ) := {x | (sepRad K')^2/4 < sepEnergy x}

/-- The inner side of the Euclidean energy separator. -/
def sepInner (K' : Set (Fin 3 → ℂ)) : Set (Fin 3 → ℂ) := {x | sepEnergy x < (sepRad K')^2/4}

lemma sepRad_pos {K' : Set (Fin 3 → ℂ)} (hK : IsClosed K') (h0 : (0 : Fin 3 → ℂ) ∉ K') :
    0 < sepRad K' := by
  classical
  unfold sepRad
  split_ifs with hne
  · exact (hK.notMem_iff_infDist_pos hne).1 h0
  · exact one_pos

lemma sep_spec {K' : Set (Fin 3 → ℂ)} (hK : IsClosed K') (h0 : (0 : Fin 3 → ℂ) ∉ K') :
    IsOpen (sepOuter K') ∧ IsOpen (sepInner K') ∧ K' ⊆ sepOuter K' ∧
      (0 : Fin 3 → ℂ) ∈ sepInner K' ∧ Disjoint (sepOuter K') (sepInner K') := by
  classical
  have hρ := sepRad_pos hK h0
  refine ⟨isOpen_lt continuous_const sepEnergy_smooth.continuous, isOpen_lt sepEnergy_smooth.continuous continuous_const,
    ?_, ?_, ?_⟩
  · intro y hy
    show (sepRad K')^2/4 < sepEnergy y
    have hne : K'.Nonempty := ⟨y, hy⟩
    have hle : Metric.infDist 0 K' ≤ ‖y‖ := by
      have := Metric.infDist_le_dist_of_mem (x := 0) hy
      simpa [dist_eq_norm, norm_neg] using this
    have heq : sepRad K' = Metric.infDist 0 K' := by unfold sepRad; rw [if_pos hne]
    rw [heq] at hρ ⊢
    have he := norm_sq_le_sepEnergy y
    nlinarith [norm_nonneg y]
  · change sepEnergy (0 : Fin 3 → ℂ) < (sepRad K')^2/4
    simp only [sepEnergy,Pi.zero_apply,Complex.normSq_zero,Finset.sum_const_zero]
    positivity
  · rw [Set.disjoint_left]
    intro x hx hx'
    have h1 : (sepRad K')^2/4 < sepEnergy x := hx
    have h2 : sepEnergy x < (sepRad K')^2/4 := hx'
    linarith

/-! ### S7a: uniform bubble deformation of the outer packing -/

/-- The compact image of the outer packing. -/
def outerK {k : ℕ} (r : Fin k → ℝ) (f : Fin k → Ambient 3 → CubicAmbient) : Set CubicAmbient :=
  ⋃ i, f i '' closedBall 3 (r i)

/-- The explicit threshold `τ`. -/
def bubbleOuterTau (A B L S m p N : ℕ) (t δ c : ℝ) (D : ℝ → ℝ) {n : ℕ} (g : Fin n → ℝ × CubicAmbient → ℝ) {k : ℕ}
    (r : Fin k → ℝ) (f : Fin k → Ambient 3 → CubicAmbient) (η : ℝ) : ℝ :=
  UMoser.time cubicBasis (cubicOuterBubblePrimitive (A := A) (B := B) L S m p N t δ c D)
    (outerK r f) η g

/-- The explicit deformed maps at parameter `ε`. -/
def bubbleOuterMaps (A B L S m p N : ℕ) (t δ c : ℝ) (D : ℝ → ℝ) (T : Set CubicAmbient) {k : ℕ}
    (r : Fin k → ℝ) (f : Fin k → Ambient 3 → CubicAmbient) (η ε : ℝ) :
    Fin k → Ambient 3 → CubicAmbient :=
  fun i => UMoser.map cubicBasis (cubicOuterBubblePrimitive (A := A) (B := B) L S m p N t δ c D)
    (outerK r f) (fun q : ℝ × CubicAmbient => q.2) ε ∘ f i

theorem bubbleOuter_spec {A B L S m p N k : ℕ} (hmp : m < p) (hN : 0 < N)
    (t δ c : ℝ) {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hD0 : (L : ℝ) * D 0 = 1)
    {T : Set CubicAmbient} (hT : IsOpen T)
    (r : Fin k → ℝ) (f : Fin k → Ambient 3 → CubicAmbient)
    (hf : ∀ i, FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
      (outerAmbientForm (A := A) (B := B) L S (D 0 * c) t δ) (f i))
    (hinto : ∀ i, MapsTo (f i) (closedBall 3 (r i)) T)
    (hd : Pairwise (fun i j => Disjoint (f i '' closedBall 3 (r i)) (f j '' closedBall 3 (r j))))
    {n : ℕ} (g : Fin n → ℝ × CubicAmbient → ℝ)
    (hgs : ∀ j, ContDiff ℝ ∞ (g j))
    (hg0 : ∀ j, ∀ x ∈ outerK r f, 0 < g j (0,x))
    (hge : ∀ q, (∀ j, 0 < g j q) → q.2 ∈ T)
    {η : ℝ} (hη : 0 < η) :
    let τ := bubbleOuterTau A B L S m p N t δ c D g r f η
    0 < τ ∧ τ ≤ η ∧ ∀ ε ∈ Ioc (0 : ℝ) τ,
      let g := bubbleOuterMaps A B L S m p N t δ c D T r f η ε
      (∀ i, FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
        (cubicOuterBubbleForm (A := A) (B := B) L S m p N t δ c D ε) (g i)) ∧
      (∀ i, MapsTo (g i) (closedBall 3 (r i)) T) ∧
      Pairwise (fun i j => Disjoint (g i '' closedBall 3 (r i)) (g j '' closedBall 3 (r j))) := by
  intro τ
  let Γ := cubicOuterBubblePrimitive (A := A) (B := B) L S m p N t δ c D
  let K : Set CubicAmbient := outerK r f
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro i
    obtain ⟨U, _hU, hKU, hs, _he, _hf⟩ := hf i
    exact (closedBall_isCompact 3 (r i)).image_of_continuousOn (hs.continuousOn.mono hKU)
  have hKT : K ⊆ T := by
    intro x hx
    obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hx
    exact hinto i hy
  have hdim : Module.finrank ℝ (Ambient 3) = Module.finrank ℝ CubicAmbient := by
    simp [Ambient, CubicAmbient, PlaneBase, Module.finrank_pi_fintype, Complex.finrank_real_complex]
  have he0 (x : CubicAmbient) : manifoldExteriorOneForm (Γ 0) x =
      outerAmbientForm (A := A) (B := B) L S (D 0 * c) t δ x := by
    change manifoldExteriorOneForm
      (cubicOuterBubblePrimitive (A := A) (B := B) L S m p N t δ c D 0) x = _
    rw [cubicOuterBubblePrimitive_zero hmp hN t δ c hD0, vector_exteriorOneForm]
    rfl
  have hinv (x : CubicAmbient) (hx : x ∈ K) :
      (manifoldExteriorOneForm (Γ 0) x).IsInvertible := by
    rw [he0]
    obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hx
    exact (hf i).target_invertible hdim hy (successorStandardForm_isInvertible 2)
  have hid : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, CubicAmbient)) 𝓘(ℝ, CubicAmbient) ∞
      (fun a : ℝ × CubicAmbient => a.2) := contMDiff_snd
  obtain ⟨hτ, hτη, hall⟩ := UMoser.spec cubicBasis
    (cubicOuterBubblePrimitive_smooth_family (A := A) (B := B) L S m p N t δ c hD) hK hinv
    isOpen_univ (subset_univ K) hη hid (fun _ _ => Topology.IsEmbedding.subtypeVal) hT
    (fun x hx => hKT hx) g hgs hg0 (fun q hq => ⟨mem_univ _,hge q hq⟩)
    (fun ε => cubicOuterBubbleForm (A := A) (B := B) L S m p N t δ c D ε) (by
      intro ε _ x _
      apply ContinuousLinearMap.ext
      intro v
      apply ContinuousLinearMap.ext
      intro w
      simp only [manifoldMapDifferential, mfderiv_eq_fderiv, fderiv_fun_id,
        vector_exteriorOneForm, ContinuousLinearMap.bilinearComp_apply,
        ContinuousLinearMap.id_apply]
      rfl)
  refine ⟨hτ, hτη, ?_⟩
  intro ε hε
  obtain ⟨W, hW, hKW, hg, he, hgT, hgf⟩ := hall ε hε
  let g := UMoser.map cubicBasis Γ K (fun q : ℝ × CubicAmbient => q.2) ε
  obtain ⟨hcomp, hdj⟩ := postcompose_form_packing (fun i => closedBall 3 (r i))
    (fun _ => successorStandardForm 2)
    (outerAmbientForm (A := A) (B := B) L S (D 0 * c) t δ)
    (cubicOuterBubbleForm (A := A) (B := B) L S m p N t δ c D ε)
    hW g hg.contMDiffOn he (by
      intro x hx v w
      rw [← he0]
      exact hgf x hx v w) f hf
    (fun i x hx => hKW (mem_iUnion.mpr ⟨i, x, hx, rfl⟩)) hd
  exact ⟨hcomp, fun i x hx => hgT (hKW (mem_iUnion.mpr ⟨i, x, hx, rfl⟩)), hdj⟩

/-! ### S7b: the large ball in the bubble chart -/

/-- The scaling family `(ε, x) ↦ ε x`. -/
def bubbleScale (q : ℝ × (Fin 3 → ℂ)) : Fin 3 → ℂ := (q.1 : ℂ) • q.2

/-- The primitive family of the bubble ball. -/
def bubbleBallPrim (L S A B p N m : ℕ) (t δ c : ℝ) (D : ℝ → ℝ) :
    ℝ → ManifoldOneForm (Fin 3 → ℂ) (Fin 3 → ℂ) :=
  fun ε => cubicBubblePrimitive (A := A) (B := B) L S (m + 1) p N t δ c (D ε) ε

/-- The image of the source ball under the Fubini–Study affine chart. -/
def bubbleBallK (m : ℕ) (c : ℝ) (D : ℝ → ℝ) (r : ℝ) : Set (Fin 3 → ℂ) :=
  complexFSAffine (D 0 * ((m + 1 : ℕ) * c)) '' closedBall 3 r

/-- The explicit threshold `σ`. -/
def bubbleBallTau (L S A B p N m : ℕ) (t δ c : ℝ) (D : ℝ → ℝ) (r : ℝ)
    {n : ℕ} (g : Fin n → ℝ × (Fin 3 → ℂ) → ℝ) (η : ℝ) : ℝ :=
  UMoser.time ambientBasis (bubbleBallPrim L S A B p N m t δ c D) (bubbleBallK m c D r) η g

/-- The explicit large-ball map at parameter `ε`. -/
def bubbleBallMap (L S A B p N m : ℕ) (t δ c : ℝ) (D : ℝ → ℝ) (r : ℝ)
    (T : Set (Fin 3 → ℂ)) (η ε : ℝ) : Ambient 3 → Ambient 3 :=
  UMoser.map ambientBasis (bubbleBallPrim L S A B p N m t δ c D) (bubbleBallK m c D r)
    bubbleScale ε ∘ complexFSAffine (D 0 * ((m + 1 : ℕ) * c))

theorem bubbleBall_spec {L S A B p N : ℕ} (m : ℕ)
    (hAS : A < S) (hS : 2 * S < L) (hB : 3 * B < L + S) (hp : p < L - S) (hN : p < N)
    (hm : m + 1 ≤ p) (t δ : ℝ) {c : ℝ} (hc : 0 < c)
    {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hD0 : 0 < D 0)
    {r : ℝ} (hr : r < Real.pi * (D 0 * ((m + 1 : ℕ) * c)))
    {T : Set (Fin 3 → ℂ)} (hT : IsOpen T) (h0T : (0 : Fin 3 → ℂ) ∈ T)
    {n : ℕ} (g : Fin n → ℝ × (Fin 3 → ℂ) → ℝ)
    (hgs : ∀ j, ContDiff ℝ ∞ (g j))
    (hg0 : ∀ j, ∀ x ∈ bubbleBallK m c D r, 0 < g j (0,x))
    (hge : ∀ q, (∀ j, 0 < g j q) → bubbleScale q ∈ T)
    {η : ℝ} (hη : 0 < η) :
    let σ := bubbleBallTau L S A B p N m t δ c D r g η
    0 < σ ∧ σ ≤ η ∧ ∀ ε ∈ Ioc (0 : ℝ) σ,
      let g := bubbleBallMap L S A B p N m t δ c D r T η ε
      FormNeighborhoodEmbedding (closedBall 3 r) (fun _ => successorStandardForm 2)
        (degreeAffineForm (L : ℝ)
          (cubicBubblePolynomial (A := A) (B := B) L S (m + 1) p N t δ ε) c (D ε)) g ∧
      MapsTo g (closedBall 3 r) T := by
  intro σ
  let a : ℝ := D 0 * ((m + 1 : ℕ) * c)
  have ha : 0 < a := mul_pos hD0 (mul_pos (by positivity) hc)
  let f : Ambient 3 → Ambient 3 := complexFSAffine a
  have hf := complexFSAffine_ball_embedding (m := 2) ha hr
  let K : Set (Fin 3 → ℂ) := bubbleBallK m c D r
  have hK : IsCompact K := by
    obtain ⟨U, _hU, hKU, hs, _he, _hf⟩ := hf
    exact (closedBall_isCompact 3 r).image_of_continuousOn (hs.continuousOn.mono hKU)
  have hscale : ContDiff ℝ ∞ bubbleScale :=
    (Complex.ofRealCLM.contDiff.comp contDiff_fst).smul contDiff_snd
  have hscaleM : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, Fin 3 → ℂ)) 𝓘(ℝ, Fin 3 → ℂ) ∞ bubbleScale := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact hscale.contMDiff
  have hemb (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) η) :
      Topology.IsEmbedding (fun x : (univ : Set (Fin 3 → ℂ)) => bubbleScale (ε, x.val)) :=
    (Homeomorph.smulOfNeZero (α := Fin 3 → ℂ) (ε : ℂ)
      (Complex.ofReal_ne_zero.mpr hε.1.ne')).isEmbedding.comp Topology.IsEmbedding.subtypeVal
  let Ω := fun ε : ℝ =>
    degreeAffineForm (L : ℝ) (cubicBubblePolynomial (A := A) (B := B) L S (m + 1) p N t δ ε) c (D ε)
  have hform (ε : ℝ) (hε : ε ∈ Ioc (0 : ℝ) η) (x : Fin 3 → ℂ)
      (_hx : x ∈ (univ : Set (Fin 3 → ℂ))) :
      manifoldExteriorOneForm (bubbleBallPrim L S A B p N m t δ c D ε) x =
        (Ω ε (bubbleScale (ε, x))).bilinearComp
        (manifoldMapDifferential (fun y : Fin 3 → ℂ => bubbleScale (ε, y)) x)
        (manifoldMapDifferential (fun y : Fin 3 → ℂ => bubbleScale (ε, y)) x) := by
    ext v w
    simp only [ContinuousLinearMap.bilinearComp_apply, manifoldMapDifferential, mfderiv_eq_fderiv]
    exact cubicBubblePrimitive_curvature hAS hS hB hp.le hm hN.le t δ c (D ε) hε.1.ne' x v w
  obtain ⟨hτ, hτη, hall⟩ := UMoser.spec ambientBasis
    (cubicBubbleVariable_smooth_family (A := A) (B := B) L S (m + 1) p N t δ c hD) hK
    (fun x _ => cubicBubblePrimitive_zero_invertible m hAS hS hB hp hN t δ hc hD0 x)
    isOpen_univ (subset_univ K) hη hscaleM hemb hT
    (by intro x _; simpa only [bubbleScale, Complex.ofReal_zero, zero_smul] using h0T) g hgs hg0 (fun q hq => ⟨mem_univ _,hge q hq⟩) Ω hform
  refine ⟨hτ, hτη, ?_⟩
  intro ε hε
  obtain ⟨W, hW, hKW, hg, he, hgT, hgf⟩ := hall ε hε
  have him : MapsTo f (closedBall 3 r) W := fun x hx => hKW ⟨x, hx, rfl⟩
  refine ⟨hf.postcompose hW hg.contMDiffOn he ?_ him, ?_⟩
  · intro x hx v w
    have hh := hgf x hx v w
    simp only [mfderiv_eq_fderiv] at hh ⊢
    have hz := cubicBubblePrimitive_zero_exterior (A := A) (B := B) m hAS hS hB hp hN t δ c
      (D 0) x v w
    refine hh.trans (hz.trans ?_)
    exact (affineFSForm_mul (D 0) ((m + 1 : ℕ) * c) (complexCartesian x)
      (complexCartesian v) (complexCartesian w)).symm
  · exact hgT.comp him

end SymplecticPacking.BranchLarge3
