import SymplecticPacking.BranchLarge3.Params
import SymplecticPacking.BranchLarge3.InnerPacking
import SymplecticPacking.BranchLarge3.CubicTransfer
import SymplecticPacking.BranchLarge3.OuterTransfer
import SymplecticPacking.BranchLarge3.Bubble
import SymplecticPacking.BranchLarge3.TargetEmbedding

/-!
# Assembly of the large-ball chain (OpenAI normalisation, target capacity 1)

The explicit composite for the input `(k, C, c)` (all parameters from `Params`):

  small family `r = rOut`, `r' = rSrc`, rational `a = aQ`, large radius `r₀ = r0`,
  `Q = bubbleQ r₀ a`,
  S1–S3  `φ_i = innerMaps Q r r' a i`                     (into `BaseCurve × ℂ²`, physical form),
  S4     `f₁_i = cubicMap … K₁ ∘ φ_i`                     (cubic ambient form, `t = cubicTime …`),
  S5     `f₂_i = outerMap … K₂ ∘ f₁_i`                    (outer form, `δ = outerDelta …`),
  S6     `m = ⌊r₀ L⌋`, `p = m + 2`, `N = m + 3`,
  S7     `ε = min τ σ / 2`, `g_i = firstToDistinguished ∘ bubbleOuterMaps … ε i`,
         `g₀ = bubbleBallMap … ε`,
  S8     `G = targetMap P L (1/π) ((1-ε)/L)`, `P = cubicBubblePolynomial … ε`,

and the final ball maps `ballMap i = G ∘ g₀` if `i` is large, `G ∘ g_i` otherwise.
`ballMaps_spec`: these are OpenAI ball embeddings of radius `rad i = ρ_i + 2η` into the open
unit-capacity ball with pairwise disjoint images. The proof follows the OpenAI chain
`actual_six_cubic_inner_normal_packing_large` → `…_avoid_axes_large` →
`actual_six_quadric_polynomial_packing_large` → `exists_cubic_bubble_separated` →
`cubic_bubble_target_packing`, split into `stage1_spec` … `stage4_spec`.
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3

open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.FiniteMoment
open scoped ContDiff Manifold Topology
open Set

variable {k : ℕ} (C : ℝ) (c : Fin k → ℝ)

/-- `Q = bubbleQ r₀ a`. -/
def chainQ : ℕ := bubbleQ (r0 C c) (aQ C c)

/-- The weights `(L, A, B, D, S)`. -/
def chainW : Weights := innerW (chainQ C c) (rOut C c) (aQ C c)

/-- The coupling constant `1/(Lπ)`. -/
def chainC0 : ℝ := 1 / (((chainW C c).L : ℝ) * Real.pi)

/-- S3: the inner maps. -/
def phiMaps : Fin k → Ambient 3 → CubicPhysicalSpace :=
  innerMaps (chainQ C c) (rOut C c) (rSrc C c) (aQ C c)

/-- The compact image `K₁` of S3. -/
def K1 : Set CubicPhysicalSpace := ⋃ i, phiMaps C c i '' closedBall 3 (rSrc C c i)

/-- S4: the degeneration time. -/
def tTime : ℝ :=
  cubicTime (chainW C c).A (chainW C c).B (chainW C c).D (chainW C c).S (chainW C c).L (K1 C c)

/-- S4: the maps into the cubic ambient model. -/
def f1Maps (i : Fin k) : Ambient 3 → CubicAmbient :=
  cubicMap (chainW C c).A (chainW C c).B (chainW C c).D (chainW C c).S (chainW C c).L (K1 C c) ∘
    phiMaps C c i

/-- The compact image `K₂` of S4. -/
def K2 : Set CubicAmbient := ⋃ i, f1Maps C c i '' closedBall 3 (rSrc C c i)

/-- S5: the tube parameter. -/
def dDelta : ℝ :=
  outerDelta (chainW C c).L (chainW C c).S (chainW C c).A (chainW C c).B (chainC0 C c) (tTime C c)
    (K2 C c)

/-- S5: the maps into the outer model. -/
def f2Maps (i : Fin k) : Ambient 3 → CubicAmbient :=
  outerMap (chainW C c).L (chainW C c).S (chainW C c).A (chainW C c).B (chainC0 C c) (tTime C c)
    (K2 C c) ∘ f1Maps C c i

/-- The compact image `K₃` of S5. -/
def K3 : Set CubicAmbient := ⋃ i, f2Maps C c i '' closedBall 3 (rSrc C c i)

/-- S6: `m = ⌊r₀ L⌋`. -/
def mOrd : ℕ := bubbleM (r0 C c) (chainW C c).L

/-- The bubble scale `D(ε) = (1 - ε)/L`. -/
def dScale (ε : ℝ) : ℝ := (1 - ε) / (chainW C c).L

/-- The separated image `K' = firstToDistinguished '' K₃`. -/
def Kprime : Set (Fin 3 → ℂ) := firstToDistinguished '' K3 C c

/-- The open set `T` of the outer packing. -/
def Tset : Set CubicAmbient := {z | z.2 ≠ 0} ∩ firstToDistinguished ⁻¹' sepOuter (Kprime C c)

/-- S7a: the outer threshold `τ`. -/
def tauOuter : ℝ :=
  bubbleOuterTau (chainW C c).A (chainW C c).B (chainW C c).L (chainW C c).S (mOrd C c + 1)
    (mOrd C c + 2) (mOrd C c + 3) (tTime C c) (dDelta C c) (1 / Real.pi) (dScale C c)
    (outerBubbleGuards (sepRad (Kprime C c))) (rSrc C c) (f2Maps C c) (1 / 2)

/-- S7b: the ball threshold `σ`. -/
def sigmaBall : ℝ :=
  bubbleBallTau (chainW C c).L (chainW C c).S (chainW C c).A (chainW C c).B (mOrd C c + 2)
    (mOrd C c + 3) (mOrd C c) (tTime C c) (dDelta C c) (1 / Real.pi) (dScale C c) (r0 C c)
    (innerBubbleGuards (sepRad (Kprime C c))) (1 / 2)

/-- S7: the bubble parameter `ε = min τ σ / 2`. -/
def epsB : ℝ := min (tauOuter C c) (sigmaBall C c) / 2

/-- S7: the small maps in the distinguished chart. -/
def gSmall (i : Fin k) : Ambient 3 → Ambient 3 :=
  firstToDistinguished ∘
    bubbleOuterMaps (chainW C c).A (chainW C c).B (chainW C c).L (chainW C c).S (mOrd C c + 1)
      (mOrd C c + 2) (mOrd C c + 3) (tTime C c) (dDelta C c) (1 / Real.pi) (dScale C c)
      (Tset C c) (rSrc C c) (f2Maps C c) (1 / 2) (epsB C c) i

/-- S7: the large-ball map. -/
def gLarge : Ambient 3 → Ambient 3 :=
  bubbleBallMap (chainW C c).L (chainW C c).S (chainW C c).A (chainW C c).B (mOrd C c + 2)
    (mOrd C c + 3) (mOrd C c) (tTime C c) (dDelta C c) (1 / Real.pi) (dScale C c) (r0 C c)
    (sepInner (Kprime C c)) (1 / 2) (epsB C c)

/-- S8: the shell map of the bubble polynomial. -/
def shell : Ambient 3 → Ambient 3 :=
  targetMap (cubicBubblePolynomial (A := (chainW C c).A) (B := (chainW C c).B) (chainW C c).L
      (chainW C c).S (mOrd C c + 1) (mOrd C c + 2) (mOrd C c + 3) (tTime C c) (dDelta C c)
      (epsB C c : ℂ))
    (chainW C c).L (1 / Real.pi) (dScale C c (epsB C c))

open Classical in
/-- **The explicit ball maps** (OpenAI normalisation). -/
def ballMap (i : Fin k) : Ambient 3 → Ambient 3 :=
  if IsLarge C c i then shell C c ∘ gLarge C c else shell C c ∘ gSmall C c i

/-! ### Specification -/

variable {C c}

lemma chainHyp (h : Hyp k C c) : ChainHyp (rOut C c) (rSrc C c) (aQ C c) :=
  ⟨h.one_le, rOut_pos h, rSrc_nonneg h, rSrc_lt_rOut h, aQ_gt_half h, aQ_lt_one h, rOut_lt h,
    sum_rOut_cube h⟩

/-- The integer inequalities of the chain (from S1, S2, S6). -/
lemma chain_ints (h : Hyp k C c) :
    0 < (chainW C c).L ∧ 0 < (chainW C c).A ∧ (chainW C c).A < (chainW C c).S ∧
      (chainW C c).A ≤ (chainW C c).B ∧ (chainW C c).S ≤ (chainW C c).B ∧
      2 * (chainW C c).S < (chainW C c).L ∧ 3 * (chainW C c).B < (chainW C c).L + (chainW C c).S ∧
      (chainW C c).D = (chainW C c).L + (chainW C c).S ∧
      ((chainW C c).S : ℝ) = ((chainW C c).L : ℝ) * (1 - (aQ C c : ℝ)) ∧
      mOrd C c + 1 < mOrd C c + 2 ∧ mOrd C c + 2 < (chainW C c).L - (chainW C c).S ∧
      r0 C c < ((mOrd C c + 1 : ℕ) : ℝ) / ((chainW C c).L : ℝ) := by
  obtain ⟨hQL, hL, hA, hS0, hAS, hAB, hSB, hB, hS, -, -, heD, heS⟩ :=
    innerW_spec (chainQ C c) (chainHyp h)
  unfold mOrd chainW
  set W := innerW (chainQ C c) (rOut C c) (aQ C c) with hWdef
  have hDLS : W.D = W.L + W.S := by
    apply Nat.cast_injective (R := ℝ); push_cast
    rw [heD, heS]; ring
  have ha := aQ_real_gt_half h
  have hLr : (0 : ℝ) < W.L := by exact_mod_cast hL
  have hSL : 2 * W.S < W.L := by
    have : 2 * (W.S : ℝ) < W.L := by rw [heS]; nlinarith
    exact_mod_cast this
  have hB' : 3 * W.B < W.L + W.S := by rw [← hDLS]; exact hB
  obtain ⟨h1, h2, -, h4⟩ := bubble_orders_spec (r0_nonneg h) (r0_lt_aQ h) hQL (by omega) heS
  exact ⟨hL, hA, hAS, hAB, hSB, hSL, hB', hDLS, heS, h1, h2, h4⟩

/-- Stage 1 (S3 → S4): the maps `f₁` into the cubic ambient model
(OpenAI `actual_six_cubic_inner_polynomial_packing_avoid_axes_large`). -/
theorem stage1_spec (h : Hyp k C c) :
    0 < tTime C c ∧
    (∀ i, FormNeighborhoodEmbedding (closedBall 3 (rSrc C c i)) (fun _ => successorStandardForm 2)
      (cubicAmbientForm (A := (chainW C c).A) (B := (chainW C c).B) (chainW C c).D (chainW C c).S
        (chainC0 C c) (tTime C c)) (f1Maps C c i)) ∧
    (∀ i, MapsTo (f1Maps C c i) (closedBall 3 (rSrc C c i)) cubicAffineDomain) ∧
    Pairwise (fun i j => Disjoint (f1Maps C c i '' closedBall 3 (rSrc C c i))
      (f1Maps C c j '' closedBall 3 (rSrc C c j))) := by
  obtain ⟨hL, hA, -, hAB, -, -, -, -, -, -, -, -⟩ := chain_ints h
  obtain ⟨-, -, hh₁, hh₂, hφ, hm, hd⟩ := inner_spec (chainQ C c) (chainHyp h)
  have hLr : (0 : ℝ) < (chainW C c).L := by exact_mod_cast hL
  have hK : IsCompact (K1 C c) := by
    apply isCompact_iUnion
    intro i
    obtain ⟨U, _hU, hKU, hs, _he, _hf⟩ := hφ i
    exact (closedBall_isCompact 3 (rSrc C c i)).image_of_continuousOn (hs.continuousOn.mono hKU)
  have hPS := physicalParameter_maps_six_region hL hh₁ hh₂
    (show ((chainW C c).A : ℝ) = ((chainW C c).L : ℝ) * (((chainW C c).A : ℝ) / (chainW C c).L) by
      field_simp)
    (show ((chainW C c).B : ℝ) = ((chainW C c).L : ℝ) * (((chainW C c).B : ℝ) / (chainW C c).L) by
      field_simp)
  have hKd (p : CubicPhysicalSpace) (hp : p ∈ K1 C c) :
      physicalParameter (chainW C c).L (planeMoments p.2) ∈
        Radial.lowerTrapezoid (chainW C c).A (chainW C c).B := by
    obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp hp
    exact hPS (interior_subset (hm i hx)).2
  have hinv (p : CubicPhysicalSpace) (hp : p ∈ K1 C c) :
      (cubicPhysicalForm (A := (chainW C c).A) (B := (chainW C c).B) (chainW C c).D (chainW C c).S
        (chainW C c).L p).IsInvertible := by
    obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp hp
    exact (hφ i).target_invertible (complexSplitPhase 2).toLinearEquiv.finrank_eq hx
      (successorStandardForm_isInvertible 2)
  obtain ⟨ht, W, hW, hKW, hg, hgemb, hgT, hgform⟩ :=
    cubicTransfer_spec hA hAB (chainW C c).D (chainW C c).S hLr hK hKd hinv
  obtain ⟨hf, hdj⟩ := postcompose_form_packing (fun i => closedBall 3 (rSrc C c i))
    (fun _ => successorStandardForm 2)
    (cubicPhysicalForm (A := (chainW C c).A) (B := (chainW C c).B) (chainW C c).D (chainW C c).S
      (chainW C c).L)
    (cubicAmbientForm (A := (chainW C c).A) (B := (chainW C c).B) (chainW C c).D (chainW C c).S
      (1 / (((chainW C c).L : ℝ) * Real.pi)) (tTime C c))
    hW _ hg hgemb hgform (phiMaps C c) hφ
    (fun i x hx => hKW (mem_iUnion.mpr ⟨i, x, hx, rfl⟩)) hd
  exact ⟨ht, hf, fun i x hx => hgT (hKW (mem_iUnion.mpr ⟨i, x, hx, rfl⟩)), hdj⟩

/-- Stage 2 (S5): the maps `f₂` into the outer model
(OpenAI `actual_six_quadric_polynomial_packing_large`). -/
theorem stage2_spec (h : Hyp k C c) :
    (∀ i, FormNeighborhoodEmbedding (closedBall 3 (rSrc C c i)) (fun _ => successorStandardForm 2)
      (outerAmbientForm (A := (chainW C c).A) (B := (chainW C c).B) (chainW C c).L (chainW C c).S
        (chainC0 C c) (tTime C c) (dDelta C c)) (f2Maps C c i)) ∧
    (∀ i, ∀ x ∈ closedBall 3 (rSrc C c i), (f2Maps C c i x).2 ≠ 0) ∧
    Pairwise (fun i j => Disjoint (f2Maps C c i '' closedBall 3 (rSrc C c i))
      (f2Maps C c j '' closedBall 3 (rSrc C c j))) := by
  obtain ⟨-, -, hAS, -, -, hS2, hB3, hDLS, -, -, -, -⟩ := chain_ints h
  obtain ⟨-, hf, hinto, hd⟩ := stage1_spec h
  rw [hDLS] at hf
  have hK : IsCompact (K2 C c) := by
    apply isCompact_iUnion
    intro i
    obtain ⟨U, _hU, hKU, hs, _he, _hf⟩ := hf i
    exact (closedBall_isCompact 3 (rSrc C c i)).image_of_continuousOn (hs.continuousOn.mono hKU)
  have hKd : K2 C c ⊆ cubicAffineDomain := by
    intro p hp
    obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp hp
    exact hinto i hx
  have hdim : Module.finrank ℝ (Ambient 3) = Module.finrank ℝ CubicAmbient := by
    simp [Ambient, CubicAmbient, PlaneBase, Module.finrank_pi_fintype,
      Complex.finrank_real_complex]
  have hinv (p : CubicAmbient) (hp : p ∈ K2 C c) :
      (cubicAmbientForm (A := (chainW C c).A) (B := (chainW C c).B)
        ((chainW C c).L + (chainW C c).S) (chainW C c).S (chainC0 C c) (tTime C c) p).IsInvertible := by
    obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp hp
    exact (hf i).target_invertible hdim hx (successorStandardForm_isInvertible 2)
  obtain ⟨hδ, W, hW, hKW, hg, he, hgT, hgform⟩ :=
    outerTransfer_spec hAS hS2 hB3 (chainC0 C c) (tTime C c) hK hKd hinv
  obtain ⟨hgφ, hdj⟩ := postcompose_form_packing (fun i => closedBall 3 (rSrc C c i))
    (fun _ => successorStandardForm 2)
    (cubicAmbientForm (A := (chainW C c).A) (B := (chainW C c).B)
      ((chainW C c).L + (chainW C c).S) (chainW C c).S (chainC0 C c) (tTime C c))
    (outerAmbientForm (A := (chainW C c).A) (B := (chainW C c).B) (chainW C c).L (chainW C c).S
      (chainC0 C c) (tTime C c) (dDelta C c))
    hW _ hg.contMDiffOn he (by
      intro x hx v w
      have hh := hgform x hx v w
      simp only [mfderiv_eq_fderiv]
      convert! hh using 1) (f1Maps C c) hf
    (fun i x hx => hKW (mem_iUnion.mpr ⟨i, x, hx, rfl⟩)) hd
  exact ⟨hgφ, fun i x hx => hgT (f1Maps C c i x) (hKW (mem_iUnion.mpr ⟨i, x, hx, rfl⟩)), hdj⟩

/-- Stage 3 (S6–S7): the separated bubble packing (OpenAI `exists_cubic_bubble_separated`). -/
theorem stage3_spec (h : Hyp k C c) :
    let P := cubicBubblePolynomial (A := (chainW C c).A) (B := (chainW C c).B) (chainW C c).L
      (chainW C c).S (mOrd C c + 1) (mOrd C c + 2) (mOrd C c + 3) (tTime C c) (dDelta C c)
      (epsB C c : ℂ)
    let Ω := degreeAffineForm ((chainW C c).L : ℝ) P (1 / Real.pi) (dScale C c (epsB C c))
    0 < epsB C c ∧ epsB C c ≤ 1 / 2 ∧
    FormNeighborhoodEmbedding (closedBall 3 (r0 C c)) (fun _ => successorStandardForm 2)
      Ω (gLarge C c) ∧
    (∀ i, FormNeighborhoodEmbedding (closedBall 3 (rSrc C c i)) (fun _ => successorStandardForm 2)
      Ω (gSmall C c i)) ∧
    (∀ i, Disjoint (gLarge C c '' closedBall 3 (r0 C c))
      (gSmall C c i '' closedBall 3 (rSrc C c i))) ∧
    Pairwise (fun i j => Disjoint (gSmall C c i '' closedBall 3 (rSrc C c i))
      (gSmall C c j '' closedBall 3 (rSrc C c j))) := by
  intro P Ω
  obtain ⟨hL, -, hAS, -, -, hS2, hB3, -, -, hm1, hm2, hr0⟩ := chain_ints h
  obtain ⟨hf, hinto, hd⟩ := stage2_spec h
  have hLr : (0 : ℝ) < (chainW C c).L := by exact_mod_cast hL
  have hD : ContDiff ℝ ∞ (dScale C c) := (contDiff_const.sub contDiff_id).div_const _
  have hD0 : dScale C c 0 = 1 / (chainW C c).L := by simp [dScale]
  have hDL : ((chainW C c).L : ℝ) * dScale C c 0 = 1 := by rw [hD0]; field_simp
  have hnorm : dScale C c 0 * (1 / Real.pi) = chainC0 C c := by
    rw [hD0]; unfold chainC0; field_simp
  let U : Set CubicAmbient := {z | z.2 ≠ 0}
  have hU : IsOpen U := isOpen_ne_fun continuous_snd continuous_const
  have hgU : ContDiffOn ℝ ∞ firstToDistinguished U := fun _ hx =>
    (firstToDistinguished_smoothAt hx).contDiffWithinAt
  have hK : IsCompact (K3 C c) := by
    apply isCompact_iUnion
    intro i
    obtain ⟨W, _hW, hKW, hs, _he, _hf⟩ := hf i
    exact (closedBall_isCompact 3 (rSrc C c i)).image_of_continuousOn (hs.continuousOn.mono hKW)
  have hKU : K3 C c ⊆ U := by
    intro x hx
    obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp hx
    exact hinto i y hy
  have hK' : IsCompact (Kprime C c) := hK.image_of_continuousOn (hgU.continuousOn.mono hKU)
  have hzero : (0 : Fin 3 → ℂ) ∉ Kprime C c := by
    rintro ⟨x, hx, he⟩
    have he0 := congrFun he 0
    exact inv_ne_zero (hKU hx) he0
  obtain ⟨hVo, hWo, hKV, h0W, hVW⟩ := sep_spec hK'.isClosed hzero
  have hT : IsOpen (Tset C c) := hgU.continuousOn.isOpen_inter_preimage hU hVo
  have hfT : ∀ i, MapsTo (f2Maps C c i) (closedBall 3 (rSrc C c i)) (Tset C c) := by
    intro i x hx
    exact ⟨hinto i x hx, hKV ⟨f2Maps C c i x, mem_iUnion.mpr ⟨i, x, hx, rfl⟩, rfl⟩⟩
  obtain ⟨hτ, hτη, houter⟩ := bubbleOuter_spec (A := (chainW C c).A) (B := (chainW C c).B)
    (N := mOrd C c + 3) hm1 (by omega) (tTime C c) (dDelta C c) (1 / Real.pi) hD hDL hT
    (rSrc C c) (f2Maps C c) (by simpa only [hnorm] using hf) hfT hd
    (outerBubbleGuards (sepRad (Kprime C c))) (outerBubbleGuards_smooth _)
    (by
      intro j x hx
      obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hx
      exact (outerBubbleGuards_positive_iff _ (0,f2Maps C c i y)).mpr (hfT i hy) j)
    (fun q hq => (outerBubbleGuards_positive_iff _ q).mp hq)
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hcap : r0 C c < Real.pi * (dScale C c 0 * ((mOrd C c + 1 : ℕ) * (1 / Real.pi))) := by
    have e : Real.pi * (dScale C c 0 * ((mOrd C c + 1 : ℕ) * (1 / Real.pi))) =
        ((mOrd C c + 1 : ℕ) : ℝ) / ((chainW C c).L : ℝ) := by
      rw [hD0]; field_simp
    rw [e]; exact hr0
  obtain ⟨hσ, hση, hbubble⟩ := bubbleBall_spec (A := (chainW C c).A) (B := (chainW C c).B)
    (p := mOrd C c + 2) (N := mOrd C c + 3) (mOrd C c) hAS hS2 hB3 hm2 (by omega) (by omega) (tTime C c) (dDelta C c)
    (one_div_pos.mpr Real.pi_pos) hD (by rw [hD0]; positivity) hcap hWo h0W
    (innerBubbleGuards (sepRad (Kprime C c))) (innerBubbleGuards_smooth _)
    (by
      intro j x hx
      have hi : sepEnergy (((0:ℝ):ℂ) • x) < (sepRad (Kprime C c))^2/4 := by
        simpa only [Complex.ofReal_zero,zero_smul,sepInner,mem_setOf_eq] using h0W
      exact (innerBubbleGuards_positive_iff _ (0,x)).mpr hi j)
    (fun q hq => (innerBubbleGuards_positive_iff _ q).mp hq)
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hε : 0 < epsB C c := half_pos (lt_min hτ hσ)
  have hετ : epsB C c ≤ tauOuter C c :=
    (half_le_self (le_of_lt (lt_min hτ hσ))).trans (min_le_left _ _)
  have hεσ : epsB C c ≤ sigmaBall C c :=
    (half_le_self (le_of_lt (lt_min hτ hσ))).trans (min_le_right _ _)
  obtain ⟨hg, hgT, hdg⟩ := houter (epsB C c) ⟨hε, hετ⟩
  obtain ⟨hg₀, hg₀W⟩ := hbubble (epsB C c) ⟨hε, hεσ⟩
  obtain ⟨hgf, hdgf⟩ := postcompose_form_packing (fun i => closedBall 3 (rSrc C c i))
    (fun _ => successorStandardForm 2)
    (cubicOuterBubbleForm (A := (chainW C c).A) (B := (chainW C c).B) (chainW C c).L (chainW C c).S
      (mOrd C c + 1) (mOrd C c + 2) (mOrd C c + 3) (tTime C c) (dDelta C c) (1 / Real.pi)
      (dScale C c) (epsB C c))
    Ω hU firstToDistinguished hgU.contMDiffOn firstToDistinguished_isEmbedding (by
      intro z hz v w
      simp only [mfderiv_eq_fderiv]
      exact firstToDistinguished_curvature hAS hS2 hB3 (by omega) (tTime C c) (dDelta C c)
        (1 / Real.pi) (dScale C c) hε.ne' hz v w)
    _ hg (fun i x hx => (hgT i hx).1) hdg
  refine ⟨hε, hετ.trans hτη, hg₀, hgf, ?_, hdgf⟩
  intro i
  exact hVW.symm.mono
    (image_subset_iff.mpr
      (show closedBall 3 (r0 C c) ⊆ gLarge C c ⁻¹' sepInner (Kprime C c) from
        fun x hx => hg₀W hx))
    (image_subset_iff.mpr
      (show closedBall 3 (rSrc C c i) ⊆ gSmall C c i ⁻¹' sepOuter (Kprime C c) from
        fun x hx => (hgT i hx).2))

/-- **The ball maps are a packing** of the balls `B(rad i)` into the open unit-capacity ball
(OpenAI `cubic_bubble_target_packing`, with the explicit S8 shell). -/
theorem ballMaps_spec (h : Hyp k C c) :
    (∀ i, IsBallEmbedding (rad C c i) (ballMap C c i)) ∧
    (∀ i, ballMap C c i '' closedBall 3 (rad C c i) ⊆ openBall 3 1) ∧
    (∀ i j, i ≠ j → Disjoint (ballMap C c i '' closedBall 3 (rad C c i))
      (ballMap C c j '' closedBall 3 (rad C c j))) := by
  classical
  obtain ⟨hL, -, hAS, -, -, hS2, hB3, -, -, -, hm2, -⟩ := chain_ints h
  obtain ⟨hε, hε2, hg₀, hg, hd₀, hdg⟩ := stage3_spec h
  have hLr : (0 : ℝ) < (chainW C c).L := by exact_mod_cast hL
  set P := cubicBubblePolynomial (A := (chainW C c).A) (B := (chainW C c).B) (chainW C c).L
    (chainW C c).S (mOrd C c + 1) (mOrd C c + 2) (mOrd C c + 3) (tTime C c) (dDelta C c)
    (epsB C c : ℂ) with hPdef
  have hP : ContDiff ℂ ∞ P := cubicBubblePolynomial_complex_smooth _ _ _
  have hPn : ∀ z, z ≠ 0 → P z ≠ 0 := fun z hz =>
    cubicBubblePolynomial_nonzero _ _ _ _ _ _ _ (Complex.ofReal_ne_zero.mpr hε.ne') hz
  have hPs : ∀ (ζ : ℂ) z, P (ζ • z) = ζ ^ (chainW C c).L • P z :=
    cubicBubblePolynomial_homogeneous hAS hS2 hB3 (by omega) _ _ _ _ _
  have hd : 0 ≤ dScale C c (epsB C c) := by
    unfold dScale; apply div_nonneg <;> linarith
  have hdℓ : ((chainW C c).L : ℝ) * dScale C c (epsB C c) < 1 := by
    unfold dScale; rw [mul_div_cancel₀ _ hLr.ne']; linarith
  obtain ⟨hGs, hGe, hGin, hGω⟩ :=
    targetMap_spec hP hPn hPs (one_div_pos.mpr Real.pi_pos) hd hdℓ
  have hshell : shell C c = targetMap P (chainW C c).L (1 / Real.pi) (dScale C c (epsB C c)) :=
    rfl
  rw [← hshell] at hGs hGe hGin hGω
  have hpost : ∀ (r : ℝ) (f : Ambient 3 → Ambient 3),
      FormNeighborhoodEmbedding (closedBall 3 r) (fun _ => successorStandardForm 2)
        (degreeAffineForm ((chainW C c).L : ℝ) P (1 / Real.pi) (dScale C c (epsB C c))) f →
      IsBallEmbedding r (shell C c ∘ f) := by
    intro r f hf
    obtain ⟨hcomp, -⟩ := postcompose_form_packing (fun _ : Unit => closedBall 3 r)
      (fun _ => successorStandardForm 2)
      (degreeAffineForm ((chainW C c).L : ℝ) P (1 / Real.pi) (dScale C c (epsB C c)))
      (fun _ => successorStandardForm 2) isOpen_univ (shell C c) hGs.contMDiff.contMDiffOn
      (hGe.comp Topology.IsEmbedding.subtypeVal) (by
        intro x _ v w
        rw [mfderiv_eq_fderiv]
        exact (successorStandardForm_apply 2 _ _).trans (hGω x v w))
      (fun _ => f) (fun _ => hf) (fun _ _ _ => mem_univ _)
      (fun i j hij => (hij (Subsingleton.elim i j)).elim)
    exact isBallEmbedding_iff_formNeighborhoodEmbedding.mpr (hcomp ())
  have himg : ∀ i, ballMap C c i '' closedBall 3 (rad C c i) =
      shell C c '' (if IsLarge C c i then gLarge C c '' closedBall 3 (r0 C c)
        else gSmall C c i '' closedBall 3 (rSrc C c i)) := by
    intro i
    by_cases hi : IsLarge C c i
    · simp only [ballMap, hi, ↓reduceIte, rad_eq_r0 h hi, Set.image_comp]
    · simp only [ballMap, hi, ↓reduceIte, rad_eq_rSrc hi, Set.image_comp]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : IsLarge C c i
    · simp only [ballMap, hi, ↓reduceIte, rad_eq_r0 h hi]
      exact hpost _ _ hg₀
    · simp only [ballMap, hi, ↓reduceIte, rad_eq_rSrc hi]
      exact hpost _ _ (hg i)
  · intro i
    rw [himg i]
    rintro _ ⟨y, -, rfl⟩
    simpa only [mul_one_div_cancel Real.pi_ne_zero] using hGin y
  · intro i j hij
    rw [himg i, himg j, Set.disjoint_image_iff hGe.injective]
    by_cases hi : IsLarge C c i <;> by_cases hj : IsLarge C c j
    · exact (hij (large_unique h hi hj)).elim
    · simp only [hi, hj, ↓reduceIte]; exact hd₀ j
    · simp only [hi, hj, ↓reduceIte]; exact (hd₀ i).symm
    · simp only [hi, hj, ↓reduceIte]; exact hdg hij

end SymplecticPacking.BranchLarge3
