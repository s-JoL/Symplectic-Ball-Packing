import SymplecticPacking.General.Ham.Linear.Realify

/-!
# Choice of the rotation angle for the Cayley path

For `U` of unitary type, `rot θ · U + 1` is invertible for at least one of the `n + 1` angles
`θ_m = π m / (n + 1)`, `m = 0, …, n`: under `z = q + i p`, `U` is a unitary `u ∈ U(n)` and
`rot θ · U + 1` is the realification of `e^{iθ} u + 1 = e^{iθ}(u + e^{-iθ})`, which is singular
only if `-e^{-iθ}` is one of the at most `n` eigenvalues of `u`; the `n + 1` numbers `e^{-iθ_m}`
are distinct. The index used is the least good `m` (a case distinction over the finitely many
propositions `det(rot θ_m · U + 1) ≠ 0`, `m ≤ n`, written as nested `if`s by `firstGood`).
-/

noncomputable section

namespace SymplecticPacking.General.Ham.Linear

open Matrix

variable {n : ℕ}

/-- `firstGood P N`: the least `m ≤ N` with `P m` if there is one (nested case distinction). -/
def firstGood (P : ℕ → Prop) : ℕ → ℕ
  | 0 => 0
  | N + 1 => open Classical in if P (firstGood P N) then firstGood P N else N + 1

theorem firstGood_spec (P : ℕ → Prop) (N : ℕ) (h : ∃ m ≤ N, P m) : P (firstGood P N) := by
  induction N with
  | zero =>
    obtain ⟨m, hm, hP⟩ := h
    obtain rfl : m = 0 := by omega
    simpa [firstGood] using hP
  | succ N ih =>
    by_cases hc : P (firstGood P N)
    · simpa only [firstGood, hc, if_true]
    · simp only [firstGood, hc, if_false]
      obtain ⟨m, hm, hP⟩ := h
      rcases Nat.lt_or_ge m (N + 1) with hlt | hge
      · exact absurd (ih ⟨m, by omega, hP⟩) hc
      · obtain rfl : m = N + 1 := by omega
        exact hP

/-- The candidate angles `θ_m = π m / (n + 1)`. -/
def angle (n m : ℕ) : ℝ := Real.pi * m / (n + 1)

/-- **Existence of a good angle.** -/
lemma angle_mem_Icc {m : ℕ} (hm : m ≤ n) : angle n m ∈ Set.Icc 0 Real.pi := by
  unfold angle
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hmn : (m : ℝ) ≤ n + 1 := by exact_mod_cast (show m ≤ n + 1 by omega)
  constructor
  · positivity
  · rw [div_le_iff₀ hn]; nlinarith [Real.pi_pos]

lemma angle_injOn : Set.InjOn (angle n) {m | m ≤ n} := by
  intro m hm m' hm' h
  unfold angle at h
  have hn : (0 : ℝ) < n + 1 := by positivity
  have := Real.pi_pos
  have h2 : (m : ℝ) = m' := by
    have h' : Real.pi * m = Real.pi * m' := by
      have := congrArg (· * ((n : ℝ) + 1)) h
      simp only [div_mul_cancel₀ _ hn.ne'] at this
      exact this
    exact mul_left_cancel₀ Real.pi_pos.ne' h'
  exact_mod_cast h2

/-- **Existence of a good angle.** -/
theorem exists_good_angle {U : Mat n} (hU : IsUnitaryType U) :
    ∃ m ≤ n, (rot (angle n m) * U + 1).det ≠ 0 := by
  set u : CSq n := U.toBlocks₁₁.map (↑) + Complex.I • U.toBlocks₂₁.map (↑)
  have hu : realify u = U := realify_of_comm_J hU.2
  set p := (-u).charpoly
  have hp0 : p ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hdeg : p.natDegree = n := by
    rw [Matrix.charpoly_natDegree_eq_dim]; simp
  set w : ℕ → ℂ := fun m => Complex.exp ((angle n m : ℂ) * Complex.I)
  set z : ℕ → ℂ := fun m => Complex.exp (((-angle n m : ℝ) : ℂ) * Complex.I)
  have hwz : ∀ m, w m * z m = 1 := fun m => by
    simp only [w, z, ← Complex.exp_add]; push_cast; ring_nf; exact Complex.exp_zero
  have hw0 : ∀ m, w m ≠ 0 := fun m => Complex.exp_ne_zero _
  by_contra hall
  push Not at hall
  -- every candidate is a root of `p`
  have hroot : ∀ m ≤ n, p.IsRoot (z m) := by
    intro m hm
    by_contra hnr
    have hev : p.eval (z m) ≠ 0 := hnr
    rw [Matrix.eval_charpoly, sub_neg_eq_add] at hev
    have hA : IsUnit (Matrix.scalar (Fin n) (z m) + u) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hev)
    have hW : IsUnit (w m • (1 : CSq n)) := by
      refine (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr ?_)
      rw [Matrix.det_smul, Matrix.det_one, mul_one]
      exact pow_ne_zero _ (hw0 m)
    have hprod : (w m • (1 : CSq n)) * (Matrix.scalar (Fin n) (z m) + u) =
        (w m • (1 : CSq n)) * u + 1 := by
      have hd : w m • (Matrix.diagonal fun _ : Fin n => z m) = 1 := by
        ext i j
        by_cases h : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, h, hwz m]
      rw [Matrix.mul_add, Matrix.scalar_apply, smul_one_mul, hd, add_comm]
    have hR : realify ((w m • (1 : CSq n)) * u + 1) = rot (angle n m) * U + 1 := by
      rw [realify_add, realify_mul, realify_one, hu, realify_smul_one]
      simp only [rot, w, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    have hunit : IsUnit (rot (angle n m) * U + 1) := by
      rw [← hR, ← hprod]
      exact (hW.mul hA).map realifyHom
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero (hall m hm)
  -- the candidates are distinct
  have hinj : Set.InjOn z (Finset.range (n + 1) : Set ℕ) := by
    intro m hm m' hm' h
    have hm1 : m ≤ n := by simpa [Nat.lt_succ_iff] using hm
    have hm1' : m' ≤ n := by simpa [Nat.lt_succ_iff] using hm'
    have hre := congrArg Complex.re h
    simp only [z, Complex.exp_ofReal_mul_I_re, Real.cos_neg] at hre
    exact angle_injOn hm1 hm1' (Real.injOn_cos (angle_mem_Icc hm1) (angle_mem_Icc hm1') hre)
  have hsub : (Finset.range (n + 1)).image z ⊆ p.roots.toFinset := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp0]
    exact hroot m (by simpa [Nat.lt_succ_iff] using hm)
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at h1
  have h2 := (Multiset.toFinset_card_le p.roots).trans (Polynomial.card_roots' p)
  omega

/-- The index of the rotation angle used for `U`. -/
def angleIndex (U : Mat n) : ℕ := firstGood (fun m => (rot (angle n m) * U + 1).det ≠ 0) n

/-- The angle used for `U`. -/
def goodAngle (U : Mat n) : ℝ := angle n (angleIndex U)

theorem goodAngle_spec {U : Mat n} (hU : IsUnitaryType U) :
    (rot (goodAngle U) * U + 1).det ≠ 0 :=
  firstGood_spec (fun m => (rot (angle n m) * U + 1).det ≠ 0) n (exists_good_angle hU)

end SymplecticPacking.General.Ham.Linear
