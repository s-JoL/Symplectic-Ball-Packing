import Mathlib

/-!
# Algebra of unit representatives

`sec:rtc` (Return to the ball), first layer: the algebra of unit representatives.

Points of `E₃` (the total space of `𝒪(3) → CP²`) are represented by `(Z, W) ∈ ℂ³ × ℂ`, unit
representatives `‖Z‖ = 1` (`nsq Z = 1`), modulo the gauge action `(c Z, c³ W)` with `|c| = 1`
(stated for any `c` with `conj c * c = 1`).
Tangent vectors of `CP²` at `[Z]` are represented in `H_Z = {ξ : Z†ξ = 0}`; `herm a b = a†b`.

Contents (supplement, the return to the ball):
* the weight-three injection `ι` (Construction cons:rtc-injection, Lemma lem:rtc-injection);
* the transport-field algebra (Construction cons:rtc-transport,
  Lemmas lem:rtc-transport-field, lem:rtc-denominator);
* the return-field algebra (Construction cons:rtc-return, Lemmas lem:rtc-graph, lem:rtc-return-field);
* the cube-root action and its fixed loci (Lemma lem:rtc-fixed),
  and the `g`-equivariance of `F`, `n`, the injection and both fields
  (algebraic part of Lemma lem:rtc-equivariant).

The real parameter `dn` stands for `d_n` (`Params.dn`); hypotheses `0 < dn`, `dn ≤ 1/3`
(or `dn < 1/3`) are added where needed.
-/

noncomputable section

namespace SymplecticPacking.Return

open Complex ComplexConjugate
open scoped Real

/-! ### Basic notation -/

/-- `ℂ³`, the space of homogeneous coordinates (representatives `Z`). -/
abbrev C3 := Fin 3 → ℂ

/-- The Fermat cubic `F(Z) = Z₀³ + Z₁³ + Z₂³`. -/
def Fpoly (Z : C3) : ℂ := Z 0 ^ 3 + Z 1 ^ 3 + Z 2 ^ 3

/-- The Hermitian product `a†b = Σ conj(a_j) b_j` (conjugate-linear in `a`). -/
def herm (a b : C3) : ℂ := ∑ j, conj (a j) * b j

/-- The squared Hermitian norm `‖Z‖² = Σ |Z_j|²`. -/
def nsq (Z : C3) : ℝ := ∑ j, normSq (Z j)

/-- The complex derivative of `F`: `dF_Z(ξ) = Σ 3 Z_j² ξ_j`. -/
def dF (Z ξ : C3) : ℂ := ∑ j, 3 * Z j ^ 2 * ξ j

lemma ofReal_normSq' (z : ℂ) : ((normSq z : ℝ) : ℂ) = conj z * z :=
  normSq_eq_conj_mul_self

lemma normSq_of_unit {c : ℂ} (hc : conj c * c = 1) : normSq c = 1 := by
  have h := ofReal_normSq' c
  rw [hc] at h
  exact_mod_cast h

lemma herm_self (a : C3) : herm a a = (nsq a : ℂ) := by
  simp [herm, nsq, ofReal_normSq']

lemma herm_smul_right (a v : C3) (c : ℂ) : herm a (c • v) = c * herm a v := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma herm_smul_left (a v : C3) (c : ℂ) : herm (c • a) v = conj c * herm a v := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma herm_add_right (a v w : C3) : herm a (v + w) = herm a v + herm a w := by
  simp only [herm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma herm_conj (a b : C3) : conj (herm a b) = herm b a := by
  simp only [herm, map_sum, map_mul, conj_conj]
  exact Finset.sum_congr rfl fun _ _ => by ring

lemma nsq_nonneg (Z : C3) : 0 ≤ nsq Z :=
  Finset.sum_nonneg fun _ _ => normSq_nonneg _

lemma nsq_smul (Z : C3) (c : ℂ) : nsq (c • Z) = normSq c * nsq Z := by
  simp [nsq, Finset.mul_sum, normSq_mul]

lemma nsq_smul_of_unit (Z : C3) {c : ℂ} (hc : conj c * c = 1) : nsq (c • Z) = nsq Z := by
  rw [nsq_smul, normSq_of_unit hc, one_mul]

/-- On the unit sphere, `Σ conj(Z_j) Z_j = 1` in `ℂ`. -/
lemma sum_conj_mul (Z : C3) (hZ : nsq Z = 1) :
    conj (Z 0) * Z 0 + conj (Z 1) * Z 1 + conj (Z 2) * Z 2 = 1 := by
  have h := herm_self Z
  rw [hZ] at h
  simpa [herm, Fin.sum_univ_three] using h

lemma normSq_le_nsq (Z : C3) (j : Fin 3) : normSq (Z j) ≤ nsq Z :=
  Finset.single_le_sum (f := fun j => normSq (Z j)) (fun _ _ => normSq_nonneg _)
    (Finset.mem_univ j)

lemma Fpoly_smul (Z : C3) (c : ℂ) : Fpoly (c • Z) = c ^ 3 * Fpoly Z := by
  simp [Fpoly]; ring

/-- The real derivative of `F` is `dF`. -/
lemma hasFDerivAt_Fpoly (Z : C3) :
    HasFDerivAt Fpoly
      (∑ j : Fin 3, (3 * Z j ^ 2) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) j))
      Z := by
  have h : ∀ j : Fin 3, HasFDerivAt (fun Z : C3 => Z j ^ 3)
      ((3 * Z j ^ 2) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℂ) j)) Z := by
    intro j
    have h1 := (hasFDerivAt_apply (𝕜 := ℝ) (f := Z) j).pow 3
    convert h1 using 1
    ext ξ <;> simp [Nat.cast_ofNat]
  have h2 := ((h 0).add (h 1)).add (h 2)
  rw [Fin.sum_univ_three]
  exact h2

lemma fderiv_Fpoly (Z ξ : C3) : fderiv ℝ Fpoly Z ξ = dF Z ξ := by
  rw [(hasFDerivAt_Fpoly Z).fderiv]
  simp [dF, Fin.sum_univ_three, mul_assoc]

/-! ### 1. The weight-three injection (cons:rtc-injection, lem:rtc-injection) -/

/-- The moment `p = π |U|²` of a point of `N` (unit representatives). -/
def pN (U : ℂ) : ℝ := π * normSq U

/-- The moment `p_W = d_n |W|² / (1 + |W|²)` of a point of `E₃`. -/
def pW (dn : ℝ) (W : ℂ) : ℝ := dn * normSq W / (1 + normSq W)

/-- The fibre part of the injection: `W = √π U / √(d_n − p)`. -/
def injW (dn : ℝ) (U : ℂ) : ℂ := ((Real.sqrt π / Real.sqrt (dn - pN U) : ℝ) : ℂ) * U

/-- The weight-three injection `ι[Z, U] = [Z, √π U / √(d_n − p)]` on unit representatives. -/
def injection (dn : ℝ) (x : C3 × ℂ) : C3 × ℂ := (x.1, injW dn x.2)

/-- The fibre part of the inverse: `U = W √(d_n − p_W) / √π`. -/
def injWinv (dn : ℝ) (W : ℂ) : ℂ := ((Real.sqrt (dn - pW dn W) / Real.sqrt π : ℝ) : ℂ) * W

/-- The inverse `[Z, W] ↦ [Z, W √(d_n − p_W)/√π]`. -/
def injectionInv (dn : ℝ) (x : C3 × ℂ) : C3 × ℂ := (x.1, injWinv dn x.2)

lemma normSq_ofReal_mul (r : ℝ) (z : ℂ) : normSq ((r : ℂ) * z) = r ^ 2 * normSq z := by
  rw [normSq_mul, normSq_ofReal]; ring

lemma pW_nonneg {dn : ℝ} (hdn : 0 ≤ dn) (W : ℂ) : 0 ≤ pW dn W :=
  div_nonneg (mul_nonneg hdn (normSq_nonneg W)) (by linarith [normSq_nonneg W])

lemma pW_lt {dn : ℝ} (hdn : 0 < dn) (W : ℂ) : pW dn W < dn := by
  have h1 : 0 < 1 + normSq W := by linarith [normSq_nonneg W]
  rw [pW, div_lt_iff₀ h1]; nlinarith

/-- `|W|² = p/(d_n − p)` for `W = ι(U)`. -/
theorem injection_normW {dn : ℝ} {U : ℂ} (hU : pN U < dn) :
    normSq (injW dn U) = pN U / (dn - pN U) := by
  have hd : 0 < dn - pN U := by linarith
  rw [injW, normSq_ofReal_mul, div_pow, Real.sq_sqrt Real.pi_pos.le, Real.sq_sqrt hd.le, pN]
  field_simp

/-- `p_W(ι U) = p`. -/
theorem injection_pW {dn : ℝ} {U : ℂ} (hU : pN U < dn) : pW dn (injW dn U) = pN U := by
  have hd : 0 < dn - pN U := by linarith
  have hdn : dn ≠ 0 := by
    have : 0 ≤ pN U := mul_nonneg Real.pi_pos.le (normSq_nonneg U)
    exact ne_of_gt (by linarith)
  rw [pW, injection_normW hU]
  field_simp
  rw [sub_add_cancel, mul_div_cancel_left₀ _ hdn]

theorem injWinv_injW {dn : ℝ} {U : ℂ} (hU : pN U < dn) : injWinv dn (injW dn U) = U := by
  have hd : 0 < dn - pN U := by linarith
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hsd : 0 < Real.sqrt (dn - pN U) := Real.sqrt_pos.mpr hd
  rw [injWinv, injection_pW hU, injW, ← mul_assoc, ← ofReal_mul]
  have : Real.sqrt (dn - pN U) / Real.sqrt π * (Real.sqrt π / Real.sqrt (dn - pN U)) = 1 := by
    field_simp
  rw [this]; simp

theorem pN_injWinv {dn : ℝ} (hdn : 0 < dn) (W : ℂ) :
    pN (injWinv dn W) = (dn - pW dn W) * normSq W := by
  have hd : 0 < dn - pW dn W := by linarith [pW_lt hdn W]
  rw [pN, injWinv, normSq_ofReal_mul, div_pow, Real.sq_sqrt hd.le, Real.sq_sqrt Real.pi_pos.le]
  field_simp

theorem pN_injWinv_eq {dn : ℝ} (hdn : 0 < dn) (W : ℂ) : pN (injWinv dn W) = pW dn W := by
  rw [pN_injWinv hdn, pW]
  have h1 : 0 < 1 + normSq W := by linarith [normSq_nonneg W]
  field_simp
  ring

theorem pN_injWinv_lt {dn : ℝ} (hdn : 0 < dn) (W : ℂ) : pN (injWinv dn W) < dn := by
  rw [pN_injWinv_eq hdn]; exact pW_lt hdn W

theorem injW_injWinv {dn : ℝ} (hdn : 0 < dn) (W : ℂ) : injW dn (injWinv dn W) = W := by
  have hd : 0 < dn - pW dn W := by linarith [pW_lt hdn W]
  have hpi : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
  have hsd : 0 < Real.sqrt (dn - pW dn W) := Real.sqrt_pos.mpr hd
  rw [injW, pN_injWinv_eq hdn, injWinv, ← mul_assoc, ← ofReal_mul]
  have : Real.sqrt π / Real.sqrt (dn - pW dn W) * (Real.sqrt (dn - pW dn W) / Real.sqrt π) = 1 := by
    field_simp
  rw [this]; simp

/-- `ι` is a bijection of `{p < d_n}` onto all of `ℂ³ × ℂ` (on each fibre `{p < d_n} → ℂ`). -/
theorem injection_bijective {dn : ℝ} (hdn : 0 < dn) :
    Set.BijOn (injection dn) {x | pN x.2 < dn} Set.univ := by
  refine Set.InvOn.bijOn (f' := injectionInv dn) ⟨?_, ?_⟩ (fun _ _ => Set.mem_univ _) ?_
  · intro x hx
    simp only [injection, injectionInv, injWinv_injW (hx)]
  · intro x _
    simp only [injection, injectionInv, injW_injWinv hdn]
  · intro x _
    exact pN_injWinv_lt hdn x.2

lemma pN_smul_of_unit {c : ℂ} (hc : conj c * c = 1) (U : ℂ) : pN (c * U) = pN U := by
  rw [pN, pN, normSq_mul, normSq_of_unit hc, one_mul]

lemma normSq_mul_of_unit {c : ℂ} (hc : conj c * c = 1) (U : ℂ) : normSq (c * U) = normSq U := by
  rw [normSq_mul, normSq_of_unit hc, one_mul]

lemma unit_pow {c : ℂ} (hc : conj c * c = 1) (k : ℕ) : conj (c ^ k) * c ^ k = 1 := by
  rw [map_pow, ← mul_pow, hc, one_pow]

/-- Well-definedness: `ι` commutes with the gauge action `(cZ, c³U)`, `|c| = 1`. -/
theorem injection_wellDefined {dn : ℝ} {c : ℂ} (hc : conj c * c = 1) (Z : C3) (U : ℂ) :
    injection dn (c • Z, c ^ 3 * U) = (c • Z, c ^ 3 * (injection dn (Z, U)).2) := by
  simp only [injection, injW, pN_smul_of_unit (unit_pow hc 3)]
  ext <;> simp <;> ring

/-- The bound used on `N_{p ≤ h}`: `|W|² ≤ h/(d_n − h)`. -/
theorem injection_normW_le {dn h : ℝ} (hh : h < dn) {U : ℂ} (hU : pN U ≤ h) :
    normSq (injW dn U) ≤ h / (dn - h) := by
  have hp0 : 0 ≤ pN U := mul_nonneg Real.pi_pos.le (normSq_nonneg U)
  rw [injection_normW (lt_of_le_of_lt hU hh)]
  have h1 : 0 < dn - pN U := by linarith
  have h2 : 0 < dn - h := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

/-! ### 2. The transport field (cons:rtc-transport, lem:rtc-transport-field) -/

/-- `n = 3 conj(Z)² − 3 conj(f) Z`, `f = F(Z)`. -/
def nvec (Z : C3) : C3 := fun j => 3 * conj (Z j) ^ 2 - 3 * conj (Fpoly Z) * Z j

/-- `G = ‖n‖²` (equal to `9 Σ|Z_j|⁴ − 9|f|²` on the unit sphere, `G_eq`). -/
def Gfun (Z : C3) : ℝ := nsq (nvec Z)

/-- Horizontal coefficient `A = 1 − 3 p_W` of `Ω_E`. -/
def Acoef (dn : ℝ) (W : ℂ) : ℝ := 1 - 3 * pW dn W

/-- Vertical coefficient `B = d_n / (1 + |W|²)²` of `Ω_E`. -/
def Bcoef (dn : ℝ) (W : ℂ) : ℝ := dn / (1 + normSq W) ^ 2

/-- The denominator `N_den = G/A + T²/B`. -/
def Nden (dn : ℝ) (Z : C3) (W : ℂ) (T : ℝ) : ℝ := Gfun Z / Acoef dn W + T ^ 2 / Bcoef dn W

/-- The transport field `(Ż, Ẇ) = (W n/(A N_den), −T W/(B N_den))` (with `Ṫ = 1`). -/
def transportField (dn : ℝ) (Z : C3) (W : ℂ) (T : ℝ) : C3 × ℂ :=
  ((W / ((Acoef dn W * Nden dn Z W T : ℝ) : ℂ)) • nvec Z,
   ((-T / (Bcoef dn W * Nden dn Z W T) : ℝ) : ℂ) * W)

lemma Gfun_nonneg (Z : C3) : 0 ≤ Gfun Z := nsq_nonneg _

lemma herm_nvec_self (Z : C3) : herm (nvec Z) (nvec Z) = (Gfun Z : ℂ) := herm_self _

/-- (i) `Z† n = 0` on the unit sphere. -/
theorem n_horizontal (Z : C3) (hZ : nsq Z = 1) : herm Z (nvec Z) = 0 := by
  have h1 := sum_conj_mul Z hZ
  simp only [herm, nvec, Fpoly, Fin.sum_univ_three, map_add, map_pow]
  linear_combination (-3 * (conj (Z 0) ^ 3 + conj (Z 1) ^ 3 + conj (Z 2) ^ 3)) * h1

/-- (i) `n† ξ = dF_Z(ξ)` for `ξ ∈ H_Z`. -/
theorem n_dF (Z ξ : C3) (hξ : herm Z ξ = 0) : herm (nvec Z) ξ = dF Z ξ := by
  simp only [herm, Fin.sum_univ_three] at hξ
  simp only [herm, nvec, dF, Fpoly, Fin.sum_univ_three, map_add, map_sub, map_mul, map_pow,
    conj_conj, map_ofNat]
  linear_combination (-3 * (Z 0 ^ 3 + Z 1 ^ 3 + Z 2 ^ 3)) * hξ

/-- (i) `‖n‖² = 9 Σ |Z_j|⁴ − 9 |f|²` on the unit sphere. -/
theorem G_eq (Z : C3) (hZ : nsq Z = 1) :
    Gfun Z = 9 * ∑ j, normSq (Z j) ^ 2 - 9 * normSq (Fpoly Z) := by
  apply ofReal_injective
  rw [← herm_nvec_self]
  have h1 := sum_conj_mul Z hZ
  simp only [herm, nvec, Fpoly, Fin.sum_univ_three, map_add, map_sub, map_mul, map_pow,
    conj_conj, map_ofNat, ofReal_sub, ofReal_mul, ofReal_add, ofReal_pow, ofReal_normSq',
    ofReal_ofNat]
  linear_combination (9 * (Z 0 ^ 3 + Z 1 ^ 3 + Z 2 ^ 3) *
    (conj (Z 0) ^ 3 + conj (Z 1) ^ 3 + conj (Z 2) ^ 3)) * h1

lemma one_add_normSq_pos (W : ℂ) : 0 < 1 + normSq W := by linarith [normSq_nonneg W]

lemma Acoef_gt {dn : ℝ} (hdn : 0 < dn) (W : ℂ) : 1 - 3 * dn < Acoef dn W := by
  rw [Acoef]; linarith [pW_lt hdn W]

lemma Acoef_pos {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) (W : ℂ) : 0 < Acoef dn W := by
  linarith [Acoef_gt hdn W]

lemma Acoef_le_one {dn : ℝ} (hdn : 0 ≤ dn) (W : ℂ) : Acoef dn W ≤ 1 := by
  rw [Acoef]; linarith [pW_nonneg hdn W]

lemma Bcoef_pos {dn : ℝ} (hdn : 0 < dn) (W : ℂ) : 0 < Bcoef dn W :=
  div_pos hdn (pow_pos (one_add_normSq_pos W) 2)

lemma Bcoef_le {dn : ℝ} (hdn : 0 ≤ dn) (W : ℂ) : Bcoef dn W ≤ dn := by
  rw [Bcoef]
  have h1 : 1 ≤ (1 + normSq W) ^ 2 := one_le_pow₀ (by linarith [normSq_nonneg W])
  exact div_le_self hdn h1

/-- (ii) The field is horizontal: `Z† Ż = 0`. -/
theorem transport_horizontal (dn : ℝ) (Z : C3) (W : ℂ) (T : ℝ) (hZ : nsq Z = 1) :
    herm Z (transportField dn Z W T).1 = 0 := by
  rw [transportField, herm_smul_right, n_horizontal Z hZ, mul_zero]

/-- (iii) Along the field, `dF_Z(Ż) = W G/(A N_den)`. -/
theorem transport_dF (dn : ℝ) (Z : C3) (W : ℂ) (T : ℝ) (hZ : nsq Z = 1) :
    dF Z (transportField dn Z W T).1 =
      W * Gfun Z / ((Acoef dn W * Nden dn Z W T : ℝ) : ℂ) := by
  rw [← n_dF Z _ (transport_horizontal dn Z W T hZ), transportField, herm_smul_right,
    herm_nvec_self]
  ring

/-- (iii) Tangency to the constraint: `d/dT (F(Z) − T W) = dF_Z(Ż) − T Ẇ − W = 0`,
equivalently `dF_Z(Ż) = W + T Ẇ`. -/
theorem transport_constraint (dn : ℝ) (Z : C3) (W : ℂ) (T : ℝ) (hZ : nsq Z = 1)
    (hA : Acoef dn W ≠ 0) (hB : Bcoef dn W ≠ 0) (hN : Nden dn Z W T ≠ 0) :
    dF Z (transportField dn Z W T).1 - T * (transportField dn Z W T).2 - W = 0 := by
  rw [transport_dF dn Z W T hZ]
  have hNdef : Nden dn Z W T * Acoef dn W * Bcoef dn W =
      Gfun Z * Bcoef dn W + T ^ 2 * Acoef dn W := by
    rw [Nden]; field_simp
  have hNc : ((Nden dn Z W T * Acoef dn W * Bcoef dn W : ℝ) : ℂ) =
      ((Gfun Z * Bcoef dn W + T ^ 2 * Acoef dn W : ℝ) : ℂ) := by rw [hNdef]
  push_cast at hNc
  have hA' : (Acoef dn W : ℂ) ≠ 0 := ofReal_ne_zero.mpr hA
  have hB' : (Bcoef dn W : ℂ) ≠ 0 := ofReal_ne_zero.mpr hB
  have hN' : (Nden dn Z W T : ℂ) ≠ 0 := ofReal_ne_zero.mpr hN
  simp only [transportField]
  push_cast
  field_simp
  linear_combination (-W) * hNc

/-- (iii) `d/dT |W|² = 2 Re(conj W · Ẇ) = −2 T |W|² / (B N_den)`. -/
theorem transport_normW (dn : ℝ) (Z : C3) (W : ℂ) (T : ℝ) :
    2 * (conj W * (transportField dn Z W T).2).re =
      -2 * T * normSq W / (Bcoef dn W * Nden dn Z W T) := by
  simp only [transportField]
  rw [mul_left_comm, ← ofReal_normSq', ← ofReal_mul, ofReal_re]
  ring

/-- (iv) Hermitian orthogonality: for the Hermitian form `h = A ξ₁†ξ₂ + B conj(ς₁) ς₂`,
`h(V, (ξ, ς)) = conj(W)/N_den · (n†ξ − T ς)`. Hence `V` is `h`-orthogonal (so
`Ω_E = (1/π) Im h`-orthogonal) to `ker ℓ = T X_T`, `ℓ(ξ, ς) = n†ξ − Tς`. -/
theorem transport_orthogonal (dn : ℝ) (Z : C3) (W : ℂ) (T : ℝ)
    (hA : Acoef dn W ≠ 0) (hB : Bcoef dn W ≠ 0) (hN : Nden dn Z W T ≠ 0) (ξ : C3) (ς : ℂ) :
    (Acoef dn W : ℂ) * herm (transportField dn Z W T).1 ξ
        + (Bcoef dn W : ℂ) * conj (transportField dn Z W T).2 * ς =
      conj W / (Nden dn Z W T : ℂ) * (herm (nvec Z) ξ - T * ς) := by
  have hA' : (Acoef dn W : ℂ) ≠ 0 := ofReal_ne_zero.mpr hA
  have hB' : (Bcoef dn W : ℂ) ≠ 0 := ofReal_ne_zero.mpr hB
  have hN' : (Nden dn Z W T : ℂ) ≠ 0 := ofReal_ne_zero.mpr hN
  simp only [transportField, herm_smul_left, map_mul, map_div₀, conj_ofReal]
  push_cast
  field_simp
  ring

/-! #### Gauge equivariance -/

lemma nvec_smul (Z : C3) {c : ℂ} (hc : conj c * c = 1) : nvec (c • Z) = conj c ^ 2 • nvec Z := by
  funext j
  simp only [nvec, Fpoly_smul, Pi.smul_apply, smul_eq_mul, map_mul, map_pow]
  linear_combination (-3 * conj c ^ 2 * conj (Fpoly Z) * Z j) * hc

lemma Gfun_smul (Z : C3) {c : ℂ} (hc : conj c * c = 1) : Gfun (c • Z) = Gfun Z := by
  rw [Gfun, nvec_smul Z hc, nsq_smul_of_unit _ (by rw [map_pow, conj_conj, ← mul_pow, mul_comm,
    hc, one_pow]), Gfun]

lemma Acoef_smul (dn : ℝ) (W : ℂ) {c : ℂ} (hc : conj c * c = 1) :
    Acoef dn (c * W) = Acoef dn W := by
  simp [Acoef, pW, normSq_mul_of_unit hc]

lemma Bcoef_smul (dn : ℝ) (W : ℂ) {c : ℂ} (hc : conj c * c = 1) :
    Bcoef dn (c * W) = Bcoef dn W := by
  simp [Bcoef, normSq_mul_of_unit hc]

lemma Nden_gauge (dn : ℝ) (Z : C3) (W : ℂ) (T : ℝ) {c : ℂ} (hc : conj c * c = 1) :
    Nden dn (c • Z) (c ^ 3 * W) T = Nden dn Z W T := by
  rw [Nden, Nden, Gfun_smul Z hc, Acoef_smul dn W (unit_pow hc 3), Bcoef_smul dn W (unit_pow hc 3)]

/-! #### Denominator (lem:rtc-denominator) -/

lemma sum_sq4_ge (Z : C3) (hZ : nsq Z = 1) : 1 / 3 ≤ ∑ j, normSq (Z j) ^ 2 := by
  simp only [nsq, Fin.sum_univ_three] at hZ
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (normSq (Z 0) - normSq (Z 1)), sq_nonneg (normSq (Z 1) - normSq (Z 2)),
    sq_nonneg (normSq (Z 0) - normSq (Z 2))]

lemma normSq_constraint {Z : C3} {W : ℂ} {T : ℝ} (hc : Fpoly Z = T * W) :
    normSq (Fpoly Z) = T ^ 2 * normSq W := by
  rw [hc, normSq_mul, normSq_ofReal]; ring

lemma Nden_ge_G {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) (Z : C3) (W : ℂ) (T : ℝ) :
    Gfun Z ≤ Nden dn Z W T := by
  have hA := Acoef_pos hdn hdn3 W
  have hA1 := Acoef_le_one hdn.le W
  have hG := Gfun_nonneg Z
  have h1 : Gfun Z ≤ Gfun Z / Acoef dn W := by
    rw [le_div_iff₀ hA]; nlinarith
  have h2 : 0 ≤ T ^ 2 / Bcoef dn W := div_nonneg (sq_nonneg T) (Bcoef_pos hdn W).le
  rw [Nden]; linarith

lemma Nden_ge_vert {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) (Z : C3) (W : ℂ) (T : ℝ) :
    T ^ 2 / dn ≤ Nden dn Z W T := by
  have h1 : 0 ≤ Gfun Z / Acoef dn W := div_nonneg (Gfun_nonneg Z) (Acoef_pos hdn hdn3 W).le
  have h2 : T ^ 2 / dn ≤ T ^ 2 / Bcoef dn W :=
    div_le_div_of_nonneg_left (sq_nonneg T) (Bcoef_pos hdn W) (Bcoef_le hdn.le W)
  rw [Nden]; linarith

/-- At `T = 0` on the constraint set (`f = 0`): `N_den ≥ G ≥ 3`. -/
theorem Nden_ge_three {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) {Z : C3} {W : ℂ}
    (hZ : nsq Z = 1) (hf : Fpoly Z = 0) : 3 ≤ Nden dn Z W 0 := by
  have := Nden_ge_G hdn hdn3 Z W 0
  have hG := G_eq Z hZ
  rw [hf, map_zero, mul_zero, sub_zero] at hG
  linarith [sum_sq4_ge Z hZ]

/-- `N_den > 0` on the constraint set `{F(Z) = T W, ‖Z‖ = 1, 0 ≤ T}`. -/
theorem Nden_pos {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) {Z : C3} {W : ℂ} {T : ℝ}
    (hZ : nsq Z = 1) (hc : Fpoly Z = T * W) (hT : 0 ≤ T) : 0 < Nden dn Z W T := by
  rcases hT.lt_or_eq with hT | hT
  · have := Nden_ge_vert hdn hdn3 Z W T
    have : 0 < T ^ 2 / dn := div_pos (pow_pos hT 2) hdn
    linarith
  · subst hT
    have := Nden_ge_three hdn hdn3 (W := W) hZ (by simpa using hc)
    linarith

/-- The threshold `T₀ = min(1, 1/(√6 max(1, W_max)))`. -/
def T0fun (Wmax : ℝ) : ℝ := min 1 (1 / (Real.sqrt 6 * max 1 Wmax))

/-- Quantitative denominator bound: `N_den ≥ min(3/2, T₀²/d_n)` if also `|W| ≤ W_max`. -/
theorem Nden_lower {dn : ℝ} (hdn : 0 < dn) (hdn3 : dn ≤ 1 / 3) {Z : C3} {W : ℂ} {T Wmax : ℝ}
    (hZ : nsq Z = 1) (hc : Fpoly Z = T * W) (hT : 0 ≤ T) (hW : ‖W‖ ≤ Wmax) :
    min (3 / 2) (T0fun Wmax ^ 2 / dn) ≤ Nden dn Z W T := by
  have hM1 : 1 ≤ max 1 Wmax := le_max_left _ _
  have hWM : ‖W‖ ≤ max 1 Wmax := hW.trans (le_max_right _ _)
  have hs6 : 0 < Real.sqrt 6 := Real.sqrt_pos.mpr (by norm_num)
  have hs6sq : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hden : 0 < Real.sqrt 6 * max 1 Wmax := mul_pos hs6 (by linarith)
  have hT0nn : 0 ≤ T0fun Wmax := le_min zero_le_one (by positivity)
  by_cases hTT : T ≤ T0fun Wmax
  · apply min_le_of_left_le
    have hT1 : T * (Real.sqrt 6 * max 1 Wmax) ≤ 1 := by
      have := hTT.trans (min_le_right _ _)
      rwa [le_div_iff₀ hden] at this
    have hnW : 0 ≤ ‖W‖ := norm_nonneg W
    have hTW : T * ‖W‖ * Real.sqrt 6 ≤ 1 := by
      have : T * ‖W‖ ≤ T * max 1 Wmax := mul_le_mul_of_nonneg_left hWM hT
      nlinarith
    have hTW2 : 6 * (T ^ 2 * normSq W) ≤ 1 := by
      rw [normSq_eq_norm_sq]
      have h0 : 0 ≤ T * ‖W‖ * Real.sqrt 6 := by positivity
      have := mul_le_mul hTW hTW h0 zero_le_one
      nlinarith
    have hG := G_eq Z hZ
    rw [normSq_constraint hc] at hG
    have := Nden_ge_G hdn hdn3 Z W T
    linarith [sum_sq4_ge Z hZ]
  · apply min_le_of_right_le
    push Not at hTT
    have := Nden_ge_vert hdn hdn3 Z W T
    have : T0fun Wmax ^ 2 / dn ≤ T ^ 2 / dn :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hT0nn hTT.le 2) hdn.le
    linarith

/-! ### 3. The return field (cons:rtc-return, lem:rtc-graph, lem:rtc-return-field) -/

/-- `u = |F(Z)|² / ‖Z‖⁶`. -/
def uFun (Z : C3) : ℝ := normSq (Fpoly Z) / nsq Z ^ 3

/-- `A_s = 1 − 3 s d_n u/(1+u)`. -/
def As (dn s : ℝ) (Z : C3) : ℝ := 1 - 3 * s * dn * (uFun Z / (1 + uFun Z))

/-- `B_s = s d_n / (1+u)²`. -/
def Bs (dn s : ℝ) (Z : C3) : ℝ := s * dn / (1 + uFun Z) ^ 2

/-- `M_s = A_s I + B_s n n†` on `H_Z`, applied to `ξ`. -/
def Ms (dn s : ℝ) (Z ξ : C3) : C3 := (As dn s Z : ℂ) • ξ + ((Bs dn s Z : ℂ) * herm (nvec Z) ξ) • nvec Z

/-- The return field `Y_s = −(d_n/2) f n / ((1+u)(A_s + B_s G))`. -/
def returnField (dn s : ℝ) (Z : C3) : C3 :=
  (-(dn / 2 : ℂ) * Fpoly Z / (((1 + uFun Z) * (As dn s Z + Bs dn s Z * Gfun Z) : ℝ) : ℂ)) • nvec Z

lemma uFun_nonneg (Z : C3) : 0 ≤ uFun Z :=
  div_nonneg (normSq_nonneg _) (pow_nonneg (nsq_nonneg Z) 3)

/-- `|f| ≤ 1` on the unit sphere. -/
theorem norm_Fpoly_le_one (Z : C3) (hZ : nsq Z = 1) : ‖Fpoly Z‖ ≤ 1 := by
  have hj : ∀ j, ‖Z j‖ ^ 3 ≤ normSq (Z j) := by
    intro j
    have h1 : normSq (Z j) ≤ 1 := hZ ▸ normSq_le_nsq Z j
    rw [normSq_eq_norm_sq] at h1 ⊢
    have h0 := norm_nonneg (Z j)
    have : ‖Z j‖ ≤ 1 := by nlinarith
    nlinarith
  have hs : ‖Fpoly Z‖ ≤ ‖Z 0‖ ^ 3 + ‖Z 1‖ ^ 3 + ‖Z 2‖ ^ 3 := by
    rw [Fpoly, ← norm_pow, ← norm_pow, ← norm_pow]
    exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
  simp only [nsq, Fin.sum_univ_three] at hZ
  linarith [hj 0, hj 1, hj 2]

/-- `u ≤ 1` on the unit sphere. -/
theorem uFun_le_one (Z : C3) (hZ : nsq Z = 1) : uFun Z ≤ 1 := by
  rw [uFun, hZ, one_pow, div_one, normSq_eq_norm_sq]
  have := norm_Fpoly_le_one Z hZ
  nlinarith [norm_nonneg (Fpoly Z)]

lemma u_div_le_half (Z : C3) (hZ : nsq Z = 1) : uFun Z / (1 + uFun Z) ≤ 1 / 2 := by
  have h0 := uFun_nonneg Z
  rw [div_le_iff₀ (by linarith)]
  linarith [uFun_le_one Z hZ]

theorem As_ge {dn s : ℝ} (hdn : 0 ≤ dn) (_hs0 : 0 ≤ s) (hs1 : s ≤ 1) (Z : C3) (hZ : nsq Z = 1) :
    1 - 3 / 2 * dn ≤ As dn s Z := by
  have h1 := u_div_le_half Z hZ
  have h0 : 0 ≤ uFun Z / (1 + uFun Z) := div_nonneg (uFun_nonneg Z) (by linarith [uFun_nonneg Z])
  have : s * dn * (uFun Z / (1 + uFun Z)) ≤ dn * (1 / 2) := by
    have := mul_le_mul hs1 h1 h0 zero_le_one
    nlinarith
  rw [As]; nlinarith

/-- `A_s > 1/2` for `0 ≤ s ≤ 1`, `0 ≤ d_n < 1/3` on the unit sphere. -/
theorem As_gt_half {dn s : ℝ} (hdn : 0 ≤ dn) (hdn3 : dn < 1 / 3) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (Z : C3) (hZ : nsq Z = 1) : 1 / 2 < As dn s Z := by
  have := As_ge hdn hs0 hs1 Z hZ; linarith

theorem Bs_nonneg {dn s : ℝ} (hdn : 0 ≤ dn) (hs0 : 0 ≤ s) (Z : C3) : 0 ≤ Bs dn s Z :=
  div_nonneg (mul_nonneg hs0 hdn) (by positivity)

lemma returnDen_gt_half {dn s : ℝ} (hdn : 0 ≤ dn) (hdn3 : dn < 1 / 3) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (Z : C3) (hZ : nsq Z = 1) : 1 / 2 < As dn s Z + Bs dn s Z * Gfun Z := by
  have := As_gt_half hdn hdn3 hs0 hs1 Z hZ
  have := mul_nonneg (Bs_nonneg hdn hs0 Z) (Gfun_nonneg Z)
  linarith

lemma Ms_smul (dn s : ℝ) (Z ξ : C3) (a : ℂ) : Ms dn s Z (a • ξ) = a • Ms dn s Z ξ := by
  funext j
  simp only [Ms, herm_smul_right, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- `n` is an eigenvector: `M_s n = (A_s + B_s G) n`. -/
theorem Ms_nvec (dn s : ℝ) (Z : C3) :
    Ms dn s Z (nvec Z) = ((As dn s Z + Bs dn s Z * Gfun Z : ℝ) : ℂ) • nvec Z := by
  rw [Ms, herm_nvec_self, ← add_smul]; push_cast; ring_nf

theorem returnField_horizontal (dn s : ℝ) (Z : C3) (hZ : nsq Z = 1) :
    herm Z (returnField dn s Z) = 0 := by
  rw [returnField, herm_smul_right, n_horizontal Z hZ, mul_zero]

/-- `M_s Y_s = −(d_n/2) f n/(1+u)`. -/
theorem Ms_returnField {dn s : ℝ} (hdn : 0 ≤ dn) (hdn3 : dn < 1 / 3) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (Z : C3) (hZ : nsq Z = 1) :
    Ms dn s Z (returnField dn s Z) =
      (-(dn / 2 : ℂ) * Fpoly Z / ((1 + uFun Z : ℝ) : ℂ)) • nvec Z := by
  have hD := returnDen_gt_half hdn hdn3 hs0 hs1 Z hZ
  have hD' : ((As dn s Z + Bs dn s Z * Gfun Z : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith)
  have hu' : ((1 + uFun Z : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (by linarith [uFun_nonneg Z])
  rw [returnField, Ms_smul, Ms_nvec, smul_smul]
  congr 1
  rw [ofReal_mul]
  field_simp

/-- The contraction formula (Lemma lem:rtc-return-field, algebraic part):
`ω_s(Y_s, ξ) = (1/π) Im((M_s Y_s)† ξ) = −d_n Im(conj(f) n†ξ)/(2π(1+u))`; the right side is
`−d_n d^c log(1+u)(ξ)` by Lemma lem:rtc-dc-horizontal. -/
theorem returnField_contract {dn s : ℝ} (hdn : 0 ≤ dn) (hdn3 : dn < 1 / 3) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (Z : C3) (hZ : nsq Z = 1) (ξ : C3) :
    1 / π * (herm (Ms dn s Z (returnField dn s Z)) ξ).im =
      -dn * ((conj (Fpoly Z) * herm (nvec Z) ξ).im / (2 * π * (1 + uFun Z))) := by
  rw [Ms_returnField hdn hdn3 hs0 hs1 Z hZ, herm_smul_left]
  have hu : 0 < 1 + uFun Z := by linarith [uFun_nonneg Z]
  have : conj (-(dn / 2 : ℂ) * Fpoly Z / ((1 + uFun Z : ℝ) : ℂ)) * herm (nvec Z) ξ =
      ((-(dn / 2) / (1 + uFun Z) : ℝ) : ℂ) * (conj (Fpoly Z) * herm (nvec Z) ξ) := by
    simp only [map_mul, map_div₀, map_neg, conj_ofReal, map_ofNat]
    push_cast; ring
  rw [this, im_ofReal_mul]
  field_simp

lemma uFun_smul (Z : C3) {c : ℂ} (hc : conj c * c = 1) : uFun (c • Z) = uFun Z := by
  rw [uFun, uFun, Fpoly_smul, nsq_smul_of_unit Z hc, normSq_mul_of_unit (unit_pow hc 3)]

lemma As_smul (dn s : ℝ) (Z : C3) {c : ℂ} (hc : conj c * c = 1) : As dn s (c • Z) = As dn s Z := by
  rw [As, As, uFun_smul Z hc]

lemma Bs_smul (dn s : ℝ) (Z : C3) {c : ℂ} (hc : conj c * c = 1) : Bs dn s (c • Z) = Bs dn s Z := by
  rw [Bs, Bs, uFun_smul Z hc]

/-- Gauge equivariance of the return field: `Y_s(cZ) = c Y_s(Z)`. -/
theorem returnField_gauge (dn s : ℝ) (Z : C3) {c : ℂ} (hc : conj c * c = 1) :
    returnField dn s (c • Z) = c • returnField dn s Z := by
  rw [returnField, returnField, uFun_smul Z hc, As_smul dn s Z hc, Bs_smul dn s Z hc,
    Gfun_smul Z hc, nvec_smul Z hc, Fpoly_smul, smul_smul, smul_smul]
  congr 1
  linear_combination (-(dn / 2 : ℂ) * Fpoly Z /
    (((1 + uFun Z) * (As dn s Z + Bs dn s Z * Gfun Z) : ℝ) : ℂ) * c * (conj c * c + 1)) * hc

/-! ### 4. The cube-root action and fixed loci (lem:rtc-fixed) -/

/-- `ζ = e^{2πi/3} = −1/2 + (√3/2) i`. -/
def zeta : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

lemma sqrt3_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

lemma conj_zeta_mul : conj zeta * zeta = 1 := by
  apply Complex.ext <;> simp [zeta] <;> nlinarith [sqrt3_sq]

lemma zeta_sq : zeta ^ 2 = conj zeta := by
  apply Complex.ext <;> simp [zeta, pow_two] <;> nlinarith [sqrt3_sq]

lemma zeta_cube : zeta ^ 3 = 1 := by
  rw [pow_succ, zeta_sq, conj_zeta_mul]

lemma conj_zeta_sq : conj zeta ^ 2 = zeta := by
  rw [← zeta_sq, ← pow_mul]
  calc zeta ^ (2 * 2) = zeta ^ 3 * zeta := by ring
    _ = zeta := by rw [zeta_cube, one_mul]

lemma zeta_ne_one : zeta ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp [zeta] at this
  norm_num at this

/-- The cube-root action `g Z = (ζ Z₀, Z₁, Z₂)` (no phase on `W` or `U`). -/
def cubeRoot (Z : C3) : C3 := ![zeta * Z 0, Z 1, Z 2]

@[simp] lemma cubeRoot_zero (Z : C3) : cubeRoot Z 0 = zeta * Z 0 := rfl
@[simp] lemma cubeRoot_one (Z : C3) : cubeRoot Z 1 = Z 1 := rfl
@[simp] lemma cubeRoot_two (Z : C3) : cubeRoot Z 2 = Z 2 := rfl

lemma Fpoly_cubeRoot (Z : C3) : Fpoly (cubeRoot Z) = Fpoly Z := by
  simp only [Fpoly, cubeRoot_zero, cubeRoot_one, cubeRoot_two, mul_pow, zeta_cube, one_mul]

lemma nsq_cubeRoot (Z : C3) : nsq (cubeRoot Z) = nsq Z := by
  simp only [nsq, Fin.sum_univ_three, cubeRoot_zero, cubeRoot_one, cubeRoot_two,
    normSq_mul_of_unit conj_zeta_mul]

lemma nvec_cubeRoot (Z : C3) : nvec (cubeRoot Z) = cubeRoot (nvec Z) := by
  funext j
  fin_cases j <;> simp [nvec, Fpoly_cubeRoot, map_mul, mul_pow, conj_zeta_sq] <;> ring

lemma Gfun_cubeRoot (Z : C3) : Gfun (cubeRoot Z) = Gfun Z := by
  rw [Gfun, nvec_cubeRoot, nsq_cubeRoot, Gfun]

lemma uFun_cubeRoot (Z : C3) : uFun (cubeRoot Z) = uFun Z := by
  rw [uFun, uFun, Fpoly_cubeRoot, nsq_cubeRoot]

/-- `ι` commutes with `g` (`g` acts on `Z` only). -/
theorem injection_equivariant (dn : ℝ) (Z : C3) (U : ℂ) :
    injection dn (cubeRoot Z, U) = (cubeRoot (injection dn (Z, U)).1, (injection dn (Z, U)).2) :=
  rfl

/-- Fixed locus of `g` on `CP²`: `[gZ] = [Z]` iff `Z₀ = 0` or `Z₁ = Z₂ = 0`. -/
theorem fixed_CP2 (Z : C3) :
    (∃ μ : ℂ, cubeRoot Z = μ • Z) ↔ (Z 0 = 0 ∨ (Z 1 = 0 ∧ Z 2 = 0)) := by
  constructor
  · rintro ⟨μ, hμ⟩
    have h0 := congrFun hμ 0
    have h1 := congrFun hμ 1
    have h2 := congrFun hμ 2
    simp only [cubeRoot_zero, cubeRoot_one, cubeRoot_two, Pi.smul_apply, smul_eq_mul] at h0 h1 h2
    by_cases hz : Z 0 = 0
    · exact Or.inl hz
    · right
      have hμz : μ = zeta := (mul_right_cancel₀ hz h0).symm
      subst hμz
      have hz1 : (1 - zeta) ≠ 0 := sub_ne_zero.mpr zeta_ne_one.symm
      constructor
      · exact (mul_eq_zero.mp (by linear_combination h1 : (1 - zeta) * Z 1 = 0)).resolve_left hz1
      · exact (mul_eq_zero.mp (by linear_combination h2 : (1 - zeta) * Z 2 = 0)).resolve_left hz1
  · rintro (h | ⟨h1, h2⟩)
    · refine ⟨1, ?_⟩
      funext j; fin_cases j <;> simp [h]
    · refine ⟨zeta, ?_⟩
      funext j; fin_cases j <;> simp [h1, h2]

lemma cubeRoot_of_zero {Z : C3} (h : Z 0 = 0) : cubeRoot Z = Z := by
  funext j; fin_cases j <;> simp [h]

/-- Fixed locus of `g` on `N = E₃|_C`: for `F(Z) = 0`, `Z ≠ 0`, the point `[Z, U]` is fixed
(`(gZ, U) = (μZ, μ³U)` for some `μ`) iff `Z₀ = 0`, and then `g` is the identity on the whole
fibre (`gZ = Z`). -/
theorem fixed_N {Z : C3} (hF : Fpoly Z = 0) (hZ : Z ≠ 0) (U : ℂ) :
    (∃ μ : ℂ, cubeRoot Z = μ • Z ∧ U = μ ^ 3 * U) ↔ Z 0 = 0 := by
  constructor
  · rintro ⟨μ, hμ, -⟩
    rcases (fixed_CP2 Z).mp ⟨μ, hμ⟩ with h | ⟨h1, h2⟩
    · exact h
    · exfalso
      have h0 : Z 0 ^ 3 = 0 := by simpa [Fpoly, h1, h2] using hF
      apply hZ
      funext j; fin_cases j <;> simp [pow_eq_zero_iff, h1, h2] at h0 ⊢ <;> exact h0
  · intro h
    exact ⟨1, by rw [one_smul, cubeRoot_of_zero h], by ring⟩

end SymplecticPacking.Return
