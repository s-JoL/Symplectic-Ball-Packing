import SymplecticPacking.General.Interface

/-!
# Branch n = 3, one large ball: normalisation and explicit parameters

Input `(k, C, c)` with `0 < C`, `c_i > 0`, `c_i + c_j < C` (`i ≠ j`), `Σ c_i³ < C³` and some
`C ≤ 2 c_j`. Everything is normalised by `C`: `ρ_i = c_i / C`.

* `IsLarge C c i :⇔ C ≤ 2 c_i`; at most one index is large (`large_unique`).
* `rhoL = Σ_i [i large] ρ_i` is the normalised large capacity (`rhoL_eq`).
* `gam = min (1 - Σ ρ_i³) (min_i gap_i)` with `gap_i = 1 - ρ_L` (large `i`) and
  `gap_i = 1 - ρ_L - ρ_i` (small `i`); `eta = gam / (100 (k+1))` is the common margin.
* The rational `a ∈ (ρ_L + 4η, ρ_L + 5η)` is given by the explicit floor formula `aQ`.
* The OpenAI-normalised radii (target capacity `1`):
  - `rOut i` (`r` in the OpenAI statements): `ρ_i + 3η` (small), `η` (dummy in the large slot);
  - `rSrc i` (`r'`): `ρ_i + 2η` (small), `η/2` (dummy);
  - `r0 = ρ_L + 2η` for the large ball;
  - `rad i = ρ_i + 2η` is the closed radius of every final ball embedding, and the
    interface data are `enlarged_i = C (ρ_i + η)`, `domain_i = C (ρ_i + 2η)`.

`params_hyp` collects the hypotheses of the OpenAI large-ball chain
(`1/2 < a < 1`, `r_i < 1 - a`, `Σ r_i³ < 1 - a³`, `r_0 < a`). No search is involved.
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3

open Problem General Finset

variable {k : ℕ}

/-- Normalised capacity `ρ_i = c_i / C`. -/
def rho (C : ℝ) (c : Fin k → ℝ) (i : Fin k) : ℝ := c i / C

/-- Ball `i` is large: `C ≤ 2 c_i`. -/
def IsLarge (C : ℝ) (c : Fin k → ℝ) (i : Fin k) : Prop := C ≤ 2 * c i

open Classical in
/-- Normalised capacity of the large ball (`0` if there is none). -/
def rhoL (C : ℝ) (c : Fin k → ℝ) : ℝ := ∑ i, if IsLarge C c i then rho C c i else 0

open Classical in
/-- Pair gap of index `i`. -/
def gap (C : ℝ) (c : Fin k → ℝ) (i : Fin k) : ℝ :=
  if IsLarge C c i then 1 - rhoL C c else 1 - rhoL C c - rho C c i

/-- Volume gap `1 - Σ ρ_i³`. -/
def volGap (C : ℝ) (c : Fin k → ℝ) : ℝ := 1 - ∑ i, rho C c i ^ 3

/-- `min_i gap_i` (and `1` for `k = 0`). -/
def pairGap (C : ℝ) (c : Fin k → ℝ) : ℝ := (univ : Finset (Fin k)).fold min 1 (gap C c)

/-- The common slack `γ`. -/
def gam (C : ℝ) (c : Fin k → ℝ) : ℝ := min (volGap C c) (pairGap C c)

/-- The common margin `η = γ / (100 (k+1))`. -/
def eta (C : ℝ) (c : Fin k → ℝ) : ℝ := gam C c / (100 * ((k : ℝ) + 1))

/-- Denominator of the rational `a`: `M = ⌈1/η⌉ + 1`, so `1/M < η`. -/
def aDen (C : ℝ) (c : Fin k → ℝ) : ℕ := ⌈1 / eta C c⌉₊ + 1

/-- The rational `a = (⌊(ρ_L + 4η) M⌋ + 1) / M ∈ (ρ_L + 4η, ρ_L + 5η)`. -/
def aQ (C : ℝ) (c : Fin k → ℝ) : ℚ :=
  ((⌊(rhoL C c + 4 * eta C c) * aDen C c⌋ + 1 : ℤ) : ℚ) / (aDen C c : ℚ)

open Classical in
/-- OpenAI radius `r_i` of the small family (dummy `η` in the large slot). -/
def rOut (C : ℝ) (c : Fin k → ℝ) (i : Fin k) : ℝ :=
  if IsLarge C c i then eta C c else rho C c i + 3 * eta C c

open Classical in
/-- OpenAI closed-source radius `r'_i` of the small family (dummy `η/2` in the large slot). -/
def rSrc (C : ℝ) (c : Fin k → ℝ) (i : Fin k) : ℝ :=
  if IsLarge C c i then eta C c / 2 else rho C c i + 2 * eta C c

/-- Closed radius of the large ball. -/
def r0 (C : ℝ) (c : Fin k → ℝ) : ℝ := rhoL C c + 2 * eta C c

/-- Closed radius of the final embedding of ball `i` (target capacity `1`). -/
def rad (C : ℝ) (c : Fin k → ℝ) (i : Fin k) : ℝ := rho C c i + 2 * eta C c

/-- Enlarged (normalised) source radius of ball `i`. -/
def enl (C : ℝ) (c : Fin k → ℝ) (i : Fin k) : ℝ := rho C c i + eta C c

/-! ### Properties under the branch hypotheses -/

/-- The hypotheses of the branch. -/
structure Hyp (k : ℕ) (C : ℝ) (c : Fin k → ℝ) : Prop where
  one_le : 1 ≤ k
  C_pos : 0 < C
  c_pos : ∀ i, 0 < c i
  pair : ∀ i j, i ≠ j → c i + c j < C
  vol : ∑ i, c i ^ 3 < C ^ 3
  large : ∃ j, C ≤ 2 * c j

section props

variable {C : ℝ} {c : Fin k → ℝ}

lemma rho_pos (h : Hyp k C c) (i : Fin k) : 0 < rho C c i := div_pos (h.c_pos i) h.C_pos

lemma sum_rho_cube (h : Hyp k C c) : ∑ i, rho C c i ^ 3 < 1 := by
  have hC := h.C_pos
  have : ∑ i, rho C c i ^ 3 = (∑ i, c i ^ 3) / C ^ 3 := by
    simp only [rho, div_pow, Finset.sum_div]
  rw [this, div_lt_one (by positivity)]
  exact h.vol

lemma rho_lt_one (h : Hyp k C c) (i : Fin k) : rho C c i < 1 := by
  have hs := sum_rho_cube h
  have hle : rho C c i ^ 3 ≤ ∑ j, rho C c j ^ 3 :=
    Finset.single_le_sum (f := fun j => rho C c j ^ 3) (fun j _ => by
      have := rho_pos h j; positivity) (Finset.mem_univ i)
  have hp := rho_pos h i
  by_contra hcon
  push Not at hcon
  have : 1 ≤ rho C c i ^ 3 := one_le_pow₀ hcon
  linarith

lemma large_unique (h : Hyp k C c) {i j : Fin k} (hi : IsLarge C c i) (hj : IsLarge C c j) :
    i = j := by
  by_contra hij
  have := h.pair i j hij
  unfold IsLarge at hi hj
  linarith

/-- The large index (chosen by unique description is not needed: we only use its existence). -/
lemma rhoL_eq (h : Hyp k C c) {j : Fin k} (hj : IsLarge C c j) : rhoL C c = rho C c j := by
  classical
  unfold rhoL
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro i _ hij
    have : ¬ IsLarge C c i := fun hi => hij (large_unique h hi hj)
    simp [this]
  · simp

lemma pair_rho (h : Hyp k C c) {i j : Fin k} (hij : i ≠ j) : rho C c i + rho C c j < 1 := by
  have hC := h.C_pos
  have := h.pair i j hij
  unfold rho
  rw [← add_div, div_lt_one hC]
  exact this

lemma half_le_rho_of_large {i : Fin k} (h : Hyp k C c) (hi : IsLarge C c i) :
    1 / 2 ≤ rho C c i := by
  have hC := h.C_pos
  unfold rho
  unfold IsLarge at hi
  rw [le_div_iff₀ hC]
  linarith

lemma half_le_rhoL (h : Hyp k C c) : 1 / 2 ≤ rhoL C c := by
  obtain ⟨j, hj⟩ := h.large
  rw [rhoL_eq h hj]
  exact half_le_rho_of_large h hj

lemma rhoL_lt_one (h : Hyp k C c) : rhoL C c < 1 := by
  obtain ⟨j, hj⟩ := h.large
  rw [rhoL_eq h hj]
  exact rho_lt_one h j

lemma gap_pos (h : Hyp k C c) (i : Fin k) : 0 < gap C c i := by
  classical
  unfold gap
  split_ifs with hi
  · linarith [rhoL_lt_one h]
  · obtain ⟨j, hj⟩ := h.large
    have hij : i ≠ j := fun e => hi (e ▸ hj)
    rw [rhoL_eq h hj]
    linarith [pair_rho h hij]

lemma pairGap_pos (h : Hyp k C c) : 0 < pairGap C c := by
  unfold pairGap
  rw [Finset.lt_fold_min]
  exact ⟨one_pos, fun i _ => gap_pos h i⟩

lemma pairGap_le_one : pairGap C c ≤ 1 := by
  unfold pairGap
  exact (Finset.fold_min_le (f := gap C c) (b := 1) (s := univ) 1).2 (Or.inl le_rfl)

lemma pairGap_le_gap (i : Fin k) : pairGap C c ≤ gap C c i := by
  unfold pairGap
  exact (Finset.fold_min_le (f := gap C c) (b := 1) (s := univ) (gap C c i)).2
    (Or.inr ⟨i, Finset.mem_univ i, le_rfl⟩)

lemma volGap_pos (h : Hyp k C c) : 0 < volGap C c := by
  unfold volGap; linarith [sum_rho_cube h]

lemma gam_pos (h : Hyp k C c) : 0 < gam C c := lt_min (volGap_pos h) (pairGap_pos h)

lemma gam_le_one : gam C c ≤ 1 := (min_le_right _ _).trans pairGap_le_one

lemma gam_le_volGap : gam C c ≤ volGap C c := min_le_left _ _

lemma gam_le_gap (i : Fin k) : gam C c ≤ gap C c i := (min_le_right _ _).trans (pairGap_le_gap i)

lemma eta_pos (h : Hyp k C c) : 0 < eta C c := by
  unfold eta; have := gam_pos h; positivity

lemma eta_mul (_h : Hyp k C c) : 100 * ((k : ℝ) + 1) * eta C c = gam C c := by
  unfold eta; field_simp

lemma eta_le (h : Hyp k C c) : 100 * eta C c ≤ gam C c := by
  have h1 := eta_mul h
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have he := eta_pos h
  nlinarith

lemma eta_small (h : Hyp k C c) : eta C c ≤ 1 / 100 := by
  have := eta_le h; have := gam_le_one (C := C) (c := c); linarith

/-- `10 η < 1 - ρ_L`. -/
lemma eta_rhoL (h : Hyp k C c) : 10 * eta C c < 1 - rhoL C c := by
  obtain ⟨j, hj⟩ := h.large
  have h1 := gam_le_gap (C := C) (c := c) j
  have h2 := eta_le h
  have h3 := eta_pos h
  unfold gap at h1
  rw [if_pos (show IsLarge C c j from hj)] at h1
  linarith

/-- `10 η < 1 - ρ_L - ρ_i` for small `i`. -/
lemma eta_small_pair (h : Hyp k C c) {i : Fin k} (hi : ¬ IsLarge C c i) :
    10 * eta C c < 1 - rhoL C c - rho C c i := by
  have h1 := gam_le_gap (C := C) (c := c) i
  have h2 := eta_le h
  have h3 := eta_pos h
  unfold gap at h1
  rw [if_neg hi] at h1
  linarith

lemma aDen_pos : 0 < aDen C c := Nat.succ_pos _

lemma inv_aDen_lt_eta (h : Hyp k C c) : 1 / (aDen C c : ℝ) < eta C c := by
  have he := eta_pos h
  have hM : 1 / eta C c < (aDen C c : ℝ) := by
    unfold aDen; push_cast
    exact lt_of_le_of_lt (Nat.le_ceil _) (lt_add_one _)
  have hMp : (0 : ℝ) < aDen C c := by exact_mod_cast aDen_pos
  rw [div_lt_iff₀ hMp]
  rw [div_lt_iff₀ he] at hM
  linarith

lemma aQ_cast : ((aQ C c : ℚ) : ℝ) =
    ((⌊(rhoL C c + 4 * eta C c) * aDen C c⌋ : ℝ) + 1) / (aDen C c : ℝ) := by
  unfold aQ; push_cast; ring

lemma aQ_bounds (h : Hyp k C c) :
    rhoL C c + 4 * eta C c < (aQ C c : ℝ) ∧ (aQ C c : ℝ) < rhoL C c + 5 * eta C c := by
  rw [aQ_cast]
  have hMp : (0 : ℝ) < aDen C c := by exact_mod_cast aDen_pos
  have hinv := inv_aDen_lt_eta h
  set x := (rhoL C c + 4 * eta C c) * (aDen C c : ℝ) with hx
  have hf1 := Int.floor_le x
  have hf2 := Int.lt_floor_add_one x
  constructor
  · rw [lt_div_iff₀ hMp]; linarith
  · rw [div_lt_iff₀ hMp]
    rw [div_lt_iff₀ hMp] at hinv
    nlinarith

lemma aQ_real_gt_half (h : Hyp k C c) : (1 : ℝ) / 2 < (aQ C c : ℝ) := by
  have := (aQ_bounds h).1; have := half_le_rhoL h; have := eta_pos h; linarith

lemma aQ_real_lt_one (h : Hyp k C c) : (aQ C c : ℝ) < 1 := by
  have := (aQ_bounds h).2; have := eta_rhoL h; have := eta_pos h; linarith

lemma aQ_gt_half (h : Hyp k C c) : (1 : ℚ) / 2 < aQ C c := by
  have h' : (((1 : ℚ) / 2 : ℚ) : ℝ) < ((aQ C c : ℚ) : ℝ) := by
    push_cast; exact aQ_real_gt_half h
  exact Rat.cast_lt.mp h'

lemma aQ_lt_one (h : Hyp k C c) : aQ C c < 1 := by
  have h' : ((aQ C c : ℚ) : ℝ) < ((1 : ℚ) : ℝ) := by
    push_cast; exact aQ_real_lt_one h
  exact Rat.cast_lt.mp h'

lemma rOut_pos (h : Hyp k C c) (i : Fin k) : 0 < rOut C c i := by
  classical
  unfold rOut; have := eta_pos h; have := rho_pos h i
  split_ifs <;> linarith

lemma rSrc_nonneg (h : Hyp k C c) (i : Fin k) : 0 ≤ rSrc C c i := by
  classical
  unfold rSrc; have := eta_pos h; have := rho_pos h i
  split_ifs <;> linarith

lemma rSrc_lt_rOut (h : Hyp k C c) (i : Fin k) : rSrc C c i < rOut C c i := by
  classical
  unfold rSrc rOut; have := eta_pos h
  split_ifs <;> linarith

lemma rOut_lt (h : Hyp k C c) (i : Fin k) : rOut C c i < 1 - (aQ C c : ℝ) := by
  classical
  have ha := (aQ_bounds h).2
  have he := eta_pos h
  unfold rOut
  split_ifs with hi
  · have := eta_rhoL h; linarith
  · have := eta_small_pair h hi; linarith

lemma rOut_le (h : Hyp k C c) (i : Fin k) : rOut C c i ≤ rho C c i + 5 * eta C c := by
  classical
  unfold rOut; have := eta_pos h; have := rho_pos h i
  split_ifs <;> linarith

/-- `(x + y)³ ≤ x³ + 7 y` for `0 ≤ x ≤ 1`, `0 ≤ y ≤ 1`. -/
lemma cube_add_le {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (x + y) ^ 3 ≤ x ^ 3 + 7 * y := by
  have h1 : x * y ≤ y := by nlinarith
  have h2 : x ^ 2 * y ≤ y := by nlinarith [mul_le_mul_of_nonneg_right h1 hx0]
  have h3 : x * y ^ 2 ≤ y := by nlinarith [mul_le_mul_of_nonneg_right h1 hy0]
  have h4 : y ^ 3 ≤ y := by nlinarith [mul_le_mul_of_nonneg_left hy1 (sq_nonneg y)]
  nlinarith

lemma rOut_cube_add (h : Hyp k C c) :
    ∑ i, rOut C c i ^ 3 + (aQ C c : ℝ) ^ 3 < 1 := by
  classical
  obtain ⟨j, hj⟩ := h.large
  have he := eta_pos h
  have he1 := eta_small h
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast h.one_le
  -- per-term bound
  have hterm : ∀ i, rOut C c i ^ 3 + (if i = j then (aQ C c : ℝ) ^ 3 else 0) ≤
      rho C c i ^ 3 + 7 * (5 * eta C c) + (if i = j then eta C c else 0) := by
    intro i
    have hr0 := (rho_pos h i).le
    have hr1 := (rho_lt_one h i).le
    have hcube : (rho C c i + 5 * eta C c) ^ 3 ≤ rho C c i ^ 3 + 7 * (5 * eta C c) :=
      cube_add_le hr0 hr1 (by linarith) (by linarith)
    by_cases hij : i = j
    · subst hij
      have hro : rOut C c i = eta C c := by
        unfold rOut; rw [if_pos (show IsLarge C c i from hj)]
      rw [hro, if_pos rfl, if_pos rfl]
      have ha := (aQ_bounds h).2
      have ha0 : 0 ≤ (aQ C c : ℝ) := by
        have := (aQ_bounds h).1; have := half_le_rhoL h; linarith
      have hrl := rhoL_eq h hj
      have hacube : (aQ C c : ℝ) ^ 3 ≤ (rho C c i + 5 * eta C c) ^ 3 := by
        rw [← hrl]; exact pow_le_pow_left₀ ha0 ha.le 3
      have he3 : eta C c ^ 3 ≤ eta C c := by nlinarith [sq_nonneg (eta C c)]
      linarith
    · rw [if_neg hij, if_neg hij, add_zero, add_zero]
      have hle : rOut C c i ^ 3 ≤ (rho C c i + 5 * eta C c) ^ 3 :=
        pow_le_pow_left₀ (rOut_pos h i).le (rOut_le h i) 3
      linarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (univ : Finset (Fin k))) => hterm i)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hvg := gam_le_volGap (C := C) (c := c)
  have hem := eta_mul h
  unfold volGap at hvg
  nlinarith

lemma sum_rOut_cube (h : Hyp k C c) : ∑ i, rOut C c i ^ 3 < 1 - (aQ C c : ℝ) ^ 3 := by
  have := rOut_cube_add h; linarith

lemma r0_nonneg (h : Hyp k C c) : 0 ≤ r0 C c := by
  unfold r0; have := half_le_rhoL h; have := eta_pos h; linarith

lemma r0_lt_aQ (h : Hyp k C c) : r0 C c < (aQ C c : ℝ) := by
  unfold r0; have := (aQ_bounds h).1; have := eta_pos h; linarith

lemma rad_eq_r0 (h : Hyp k C c) {i : Fin k} (hi : IsLarge C c i) : rad C c i = r0 C c := by
  unfold rad r0; rw [rhoL_eq h hi]

lemma rad_eq_rSrc {i : Fin k} (hi : ¬ IsLarge C c i) : rad C c i = rSrc C c i := by
  classical
  unfold rad rSrc; rw [if_neg hi]

lemma enl_lt_rad (h : Hyp k C c) (i : Fin k) : enl C c i < rad C c i := by
  unfold enl rad; have := eta_pos h; linarith

lemma lt_enl (h : Hyp k C c) (i : Fin k) : c i < C * enl C c i := by
  have hC := h.C_pos
  unfold enl rho
  rw [mul_add, mul_div_cancel₀ _ hC.ne']
  have := eta_pos h
  nlinarith

end props

end SymplecticPacking.BranchLarge3
