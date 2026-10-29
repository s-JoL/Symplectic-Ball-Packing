import SymplecticPacking.Strip.Embed
import SymplecticPacking.Return.Central
import SymplecticPacking.Bundle.BPoints

/-!
# The deck transformations of the coordinate model of the normal bundle

`sec:rtc-packing` (proof of `prop:rtc-embeddings` (1)–(2)): the deck transformations of the `Zunit`-frame coordinate
model of `N`, and injectivity of `Ncoord` modulo deck and gauge.

Coordinates on the cover `E4`: `(x, y, u, v)` = indices `(0, 1, 2, 3)`, `w = x + iy = wL X`.
`Ncoord X = (Zunit u v, w)` (`Return/Central.lean`). The theta lift has automorphy
(`Bundle.Zraw_automorphy`) `Zraw(z+1) = -Zraw z`, `Zraw(z+τ) = φ(πz)³ Zraw z`
(`φ = thetaFactor`), hence for the unit lift
* `Zunit (u+1) v = (-1) • Zunit u v`,
* `Zunit u (v+1) = κ(u,v) • Zunit u v`, `κ(u,v) = φ³/|φ³|`, `φ = thetaFactor (π (u + τ v))`
  (`deckFactor`).
The fibre coordinate is a section of the weight-three bundle, so it transforms with the cube of
the gauge factor. The deck maps are therefore
* `deckU (w, u, v) = (-w, u + 1, v)`,
* `deckV (w, u, v) = (κ(u,v)³ w, u, v + 1)`,
and `Ncoord (deckU X) = (-1)·Ncoord X`, `Ncoord (deckV X) = κ·Ncoord X` (gauge action
`c·(Z, U) = (cZ, c³U)`).

Main results:
* `DeckEquivariant Φ⁻¹`: the hypothesis `Φ⁻¹ ∘ deckU = deckU ∘ Φ⁻¹`, `Φ⁻¹ ∘ deckV = deckV ∘ Φ⁻¹`.
* `IsDeck Φ⁻¹ T m n`: `T` shifts `(u, v)` by `(m, n)`, acts on `Ncoord` by a unit gauge factor
  and commutes with `Φ⁻¹`; `exists_isDeck`: every `(m, n) ∈ ℤ²` is realised.
* `gauge_imp_deck`: `Ncoord A = μ · Ncoord B` (`|μ| = 1`) forces `A = T B` for a deck map `T`
  (projective injectivity of the torus, `Bundle.torusPoint_proj_injective`).
* `IsDeck.eq_of_band`: a deck map relating two points of the band
  `(1/8, 5/24) × (1/8, 5/24)` is the identity on them.
-/

noncomputable section

namespace SymplecticPacking.Embed

open _root_.Complex ComplexConjugate Set
open SymplecticPacking.Bundle (Zunit Zraw torusZ thetaFactor normSq3 normSq3_Zunit torusPoint
  latticeLift tau)
open SymplecticPacking.Handle (mk wL mk_wL)
open SymplecticPacking.Return (Ncoord C3)
open scoped Real

/-! ### Unit gauge factors -/

lemma unit_div_norm {c : ℂ} (hc : c ≠ 0) : conj (c / (‖c‖ : ℂ)) * (c / (‖c‖ : ℂ)) = 1 := by
  have hn : (‖c‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hc)
  rw [map_div₀, conj_ofReal, div_mul_div_comm, conj_mul']
  field_simp

lemma unit_mul {a b : ℂ} (ha : conj a * a = 1) (hb : conj b * b = 1) :
    conj (a * b) * (a * b) = 1 := by
  rw [map_mul]; linear_combination (conj b * b) * ha + hb

lemma unit_conj {a : ℂ} (ha : conj a * a = 1) : conj (conj a) * conj a = 1 := by
  rw [conj_conj, mul_comm]; exact ha

lemma unit_ne_zero {a : ℂ} (ha : conj a * a = 1) : a ≠ 0 := by
  rintro rfl; simp at ha

/-! ### The unit lift under the lattice translations -/

lemma normSq3_smul (c : ℂ) (Z : Fin 3 → ℂ) : normSq3 (c • Z) = ‖c‖ ^ 2 * normSq3 Z := by
  simp only [normSq3, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum]

lemma sqrt_normSq3_Zraw_pos (z : ℂ) : 0 < Real.sqrt (normSq3 (Zraw z)) :=
  Real.sqrt_pos.mpr (Bundle.normSq3_pos (Bundle.Zraw_ne_zero z))

/-- `Zraw = ‖Zraw‖ • Zunit`. -/
lemma Zraw_eq_smul_Zunit (u v : ℝ) :
    Zraw (torusZ u v) = ((Real.sqrt (normSq3 (Zraw (torusZ u v))) : ℝ) : ℂ) • Zunit u v := by
  have hs := (sqrt_normSq3_Zraw_pos (torusZ u v)).ne'
  have hs' : ((Real.sqrt (normSq3 (Zraw (torusZ u v))) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hs
  rw [Zunit, smul_smul, ← ofReal_inv, ← ofReal_mul, mul_inv_cancel₀ hs, ofReal_one, one_smul]

/-- If `Zraw` gets multiplied by `c ≠ 0`, `Zunit` gets multiplied by `c/|c|`. -/
lemma Zunit_of_Zraw_smul {u v u' v' : ℝ} {c : ℂ} (hc : c ≠ 0)
    (h : Zraw (torusZ u' v') = c • Zraw (torusZ u v)) :
    Zunit u' v' = (c / (‖c‖ : ℂ)) • Zunit u v := by
  have hs := (sqrt_normSq3_Zraw_pos (torusZ u v)).ne'
  have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  unfold Zunit
  rw [h, normSq3_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), smul_smul,
    smul_smul]
  congr 1
  push_cast
  field_simp

lemma torusZ_add_one (u v : ℝ) : torusZ (u + 1) v = torusZ u v + 1 := by
  simp only [torusZ]; push_cast; ring

lemma torusZ_add_one_v (u v : ℝ) : torusZ u (v + 1) = torusZ u v + tau := by
  simp only [torusZ]; push_cast; ring

/-- The gauge factor of the `τ`-translation: `κ(u,v) = φ³/|φ³|`, `φ = thetaFactor(π(u + τv))`. -/
def deckFactor (u v : ℝ) : ℂ :=
  thetaFactor (π * torusZ u v) ^ 3 / (‖thetaFactor (π * torusZ u v) ^ 3‖ : ℂ)

lemma deckFactor_unit (u v : ℝ) : conj (deckFactor u v) * deckFactor u v = 1 :=
  unit_div_norm (Bundle.Zraw_automorphy (torusZ u v)).2.2

theorem Zunit_add_one_u (u v : ℝ) : Zunit (u + 1) v = (-1 : ℂ) • Zunit u v := by
  have h : Zraw (torusZ (u + 1) v) = (-1 : ℂ) • Zraw (torusZ u v) := by
    rw [torusZ_add_one]; exact Bundle.Zraw_add_one _
  rw [Zunit_of_Zraw_smul (by norm_num) h]
  norm_num

theorem Zunit_add_one_v (u v : ℝ) : Zunit u (v + 1) = deckFactor u v • Zunit u v := by
  have h : Zraw (torusZ u (v + 1)) = thetaFactor (π * torusZ u v) ^ 3 • Zraw (torusZ u v) := by
    rw [torusZ_add_one_v]; exact Bundle.Zraw_add_tau _
  exact Zunit_of_Zraw_smul (Bundle.Zraw_automorphy (torusZ u v)).2.2 h

lemma Zunit_ne_zero (u v : ℝ) : Zunit u v ≠ 0 := by
  intro h
  have := normSq3_Zunit u v
  rw [h] at this
  simp [normSq3] at this

/-! ### `Zraw` is a nonzero multiple of the torus point; `F(Zunit) = 0` -/

theorem Zraw_eq_smul_torusPoint (z : ℂ) : ∃ k : ℂ, k ≠ 0 ∧ Zraw z = k • torusPoint z := by
  classical
  by_cases hθ : Bundle.jacobiTheta1 (π * z) = 0
  · have hz := (Bundle.jacobiTheta1_pi_mul_eq_zero_iff z).mp hθ
    have hd := Bundle.dTheta1_ne_zero_of_eq_zero hθ
    refine ⟨2 * Bundle.dF * π ^ 3 * Bundle.dTheta1 (π * z) ^ 3, ?_, ?_⟩
    · simp [Bundle.dF_ne_zero, hd, Real.pi_ne_zero]
    · have ht : torusPoint z = latticeLift := by simp [torusPoint, hz]
      rw [ht]
      ext i
      fin_cases i <;> simp [Bundle.Zraw, latticeLift, Bundle.PTheta, Bundle.QTheta, hθ] <;> ring
  · have hz : z ∉ Bundle.hexPair.lattice := fun h =>
      hθ ((Bundle.jacobiTheta1_pi_mul_eq_zero_iff z).mpr h)
    refine ⟨Bundle.jacobiTheta1 (π * z) ^ 3, pow_ne_zero 3 hθ, ?_⟩
    rw [Bundle.Zraw_eq hθ]
    simp [torusPoint, hz]

/-- The unit lift lies on the Fermat cubic `C = {F = 0}`. -/
theorem Fpoly_Zunit (u v : ℝ) : Return.Fpoly (Zunit u v) = 0 := by
  obtain ⟨k, -, hk⟩ := Zraw_eq_smul_torusPoint (torusZ u v)
  have hF : Return.Fpoly (torusPoint (torusZ u v)) = 0 :=
    (Bundle.torusPoint_mem (torusZ u v)).2
  rw [Zunit, hk, smul_smul, Return.Fpoly_smul, hF, mul_zero]

/-- **Projective injectivity of `Zunit` on the torus**: proportional unit lifts come from
`ℤ²`-translates. -/
theorem Zunit_proj {u v u' v' : ℝ} {μ : ℂ} (hμ : μ ≠ 0) (h : Zunit u v = μ • Zunit u' v') :
    ∃ m n : ℤ, u' = u + m ∧ v' = v + n := by
  obtain ⟨k, hk0, hk⟩ := Zraw_eq_smul_torusPoint (torusZ u v)
  obtain ⟨k', hk0', hk'⟩ := Zraw_eq_smul_torusPoint (torusZ u' v')
  set s : ℂ := ((Real.sqrt (normSq3 (Zraw (torusZ u v))) : ℝ) : ℂ)
  set s' : ℂ := ((Real.sqrt (normSq3 (Zraw (torusZ u' v'))) : ℝ) : ℂ)
  have hs : s ≠ 0 := ofReal_ne_zero.mpr (sqrt_normSq3_Zraw_pos _).ne'
  have hs' : s' ≠ 0 := ofReal_ne_zero.mpr (sqrt_normSq3_Zraw_pos _).ne'
  have e1 := Zraw_eq_smul_Zunit u v
  have e2 := Zraw_eq_smul_Zunit u' v'
  have key : torusPoint (torusZ u v) =
      (k⁻¹ * s * μ * s'⁻¹ * k') • torusPoint (torusZ u' v') := by
    have a1 : torusPoint (torusZ u v) = k⁻¹ • Zraw (torusZ u v) := by
      rw [hk, smul_smul, inv_mul_cancel₀ hk0, one_smul]
    have a2 : Zunit u' v' = s'⁻¹ • Zraw (torusZ u' v') := by
      rw [e2, smul_smul, inv_mul_cancel₀ hs', one_smul]
    rw [a1, e1, h, a2, hk']
    simp only [smul_smul]
    congr 1
    simp only [s]
    ring
  have hmem := Bundle.torusPoint_proj_injective (z := torusZ u' v') (w := torusZ u v)
    ⟨_, by simp [hk0, hs, hμ, hs', hk0'], key⟩
  exact (Bundle.torusZ_sub_mem_iff u' v' u v).mp hmem

/-! ### The deck maps -/

/-- **Deck map of `u ↦ u + 1`**: `(w, u, v) ↦ (-w, u + 1, v)`. -/
def deckU (X : E4) : E4 := mk (-wL X) (X 2 + 1) (X 3)

/-- **Deck map of `v ↦ v + 1`**: `(w, u, v) ↦ (κ(u,v)³ w, u, v + 1)`. -/
def deckV (X : E4) : E4 := mk (deckFactor (X 2) (X 3) ^ 3 * wL X) (X 2) (X 3 + 1)

/-- The inverse of `deckU`. -/
def deckUinv (X : E4) : E4 := mk (-wL X) (X 2 - 1) (X 3)

/-- The inverse of `deckV`. -/
def deckVinv (X : E4) : E4 := mk (conj (deckFactor (X 2) (X 3 - 1)) ^ 3 * wL X) (X 2) (X 3 - 1)

lemma deckU_deckUinv (X : E4) : deckU (deckUinv X) = X := by
  simp [deckU, deckUinv]

lemma deckUinv_deckU (X : E4) : deckUinv (deckU X) = X := by
  simp [deckU, deckUinv]

lemma deckV_deckVinv (X : E4) : deckV (deckVinv X) = X := by
  have hu := deckFactor_unit (X 2) (X 3 - 1)
  have : deckFactor (X 2) (X 3 - 1) ^ 3 * (conj (deckFactor (X 2) (X 3 - 1)) ^ 3 * wL X) =
      wL X := by
    linear_combination (wL X * ((conj (deckFactor (X 2) (X 3 - 1)) *
      deckFactor (X 2) (X 3 - 1)) ^ 2 + conj (deckFactor (X 2) (X 3 - 1)) *
      deckFactor (X 2) (X 3 - 1) + 1)) * hu
  simp only [deckV, deckVinv, Handle.mk_apply2, Handle.mk_apply3, Handle.wL_mk, sub_add_cancel,
    this, mk_wL]

lemma deckVinv_deckV (X : E4) : deckVinv (deckV X) = X := by
  have hu := deckFactor_unit (X 2) (X 3)
  have : conj (deckFactor (X 2) (X 3)) ^ 3 * (deckFactor (X 2) (X 3) ^ 3 * wL X) = wL X := by
    linear_combination (wL X * ((conj (deckFactor (X 2) (X 3)) *
      deckFactor (X 2) (X 3)) ^ 2 + conj (deckFactor (X 2) (X 3)) *
      deckFactor (X 2) (X 3) + 1)) * hu
  simp only [deckV, deckVinv, Handle.mk_apply2, Handle.mk_apply3, Handle.wL_mk, add_sub_cancel_right,
    this, mk_wL]

/-- **The deck-equivariance hypothesis on the Moser map** (`prop:shd4-moser`: the Moser field
is invariant under the deck group of the cover `E4 → N`): `Φ⁻¹` commutes with `deckU` and
`deckV`. -/
structure DeckEquivariant (PhiInv : E4 → E4) : Prop where
  commU : ∀ X, PhiInv (deckU X) = deckU (PhiInv X)
  commV : ∀ X, PhiInv (deckV X) = deckV (PhiInv X)

/-! ### Deck maps with a given shift -/

lemma Ncoord_eq (X : E4) : Ncoord X = (Zunit (X 2) (X 3), wL X) := by
  refine Prod.ext rfl ?_
  apply Complex.ext <;> simp [Ncoord]

/-- `T` is a deck map shifting `(u, v)` by `(m, n)`, acting on `Ncoord` by a unit gauge factor,
and commuting with `Φ⁻¹`. -/
structure IsDeck (PhiInv T : E4 → E4) (m n : ℤ) : Prop where
  shift2 : ∀ X, T X 2 = X 2 + m
  shift3 : ∀ X, T X 3 = X 3 + n
  gauge : ∀ X, ∃ c : ℂ, conj c * c = 1 ∧
    Zunit (T X 2) (T X 3) = c • Zunit (X 2) (X 3) ∧ wL (T X) = c ^ 3 * wL X
  comm : ∀ X, PhiInv (T X) = T (PhiInv X)

variable {PhiInv : E4 → E4}

lemma E4_ext3 {A B : E4} (hw : wL A = wL B) (h2 : A 2 = B 2) (h3 : A 3 = B 3) : A = B := by
  rw [← mk_wL A, ← mk_wL B, hw, h2, h3]

lemma IsDeck.of_eq {T : E4 → E4} {m n m' n' : ℤ} (h : IsDeck PhiInv T m n) (hm : m = m')
    (hn : n = n') : IsDeck PhiInv T m' n' := by
  subst hm hn; exact h

lemma isDeck_id : IsDeck PhiInv id 0 0 :=
  ⟨fun X => by simp, fun X => by simp, fun X => ⟨1, by simp, by simp, by simp⟩, fun X => rfl⟩

lemma IsDeck.comp {T S : E4 → E4} {m n m' n' : ℤ} (hT : IsDeck PhiInv T m n)
    (hS : IsDeck PhiInv S m' n') : IsDeck PhiInv (T ∘ S) (m' + m) (n' + n) where
  shift2 X := by simp only [Function.comp, hT.shift2, hS.shift2]; push_cast; ring
  shift3 X := by simp only [Function.comp, hT.shift3, hS.shift3]; push_cast; ring
  gauge X := by
    obtain ⟨c, hc, hZ, hw⟩ := hS.gauge X
    obtain ⟨d, hd, hZ', hw'⟩ := hT.gauge (S X)
    refine ⟨d * c, unit_mul hd hc, ?_, ?_⟩
    · simp only [Function.comp]; rw [hZ', hZ, smul_smul]
    · simp only [Function.comp]; rw [hw', hw]; ring
  comm X := by simp only [Function.comp, hT.comm, hS.comm]

lemma IsDeck.inv {T S : E4 → E4} {m n : ℤ} (hT : IsDeck PhiInv T m n)
    (h1 : ∀ X, T (S X) = X) (h2 : ∀ X, S (T X) = X) : IsDeck PhiInv S (-m) (-n) where
  shift2 X := by
    have := hT.shift2 (S X); rw [h1] at this; push_cast; linarith
  shift3 X := by
    have := hT.shift3 (S X); rw [h1] at this; push_cast; linarith
  gauge X := by
    obtain ⟨c, hc, hZ, hw⟩ := hT.gauge (S X)
    rw [h1] at hZ hw
    refine ⟨conj c, unit_conj hc, ?_, ?_⟩
    · rw [hZ, smul_smul, hc, one_smul]
    · rw [hw]; linear_combination (-(wL (S X)) * ((conj c * c) ^ 2 + conj c * c + 1)) * hc
  comm X := by
    calc PhiInv (S X) = S (T (PhiInv (S X))) := (h2 _).symm
      _ = S (PhiInv (T (S X))) := by rw [hT.comm]
      _ = S (PhiInv X) := by rw [h1]

lemma isDeck_deckU (hD : DeckEquivariant PhiInv) : IsDeck PhiInv deckU 1 0 where
  shift2 X := by simp [deckU]
  shift3 X := by simp [deckU]
  gauge X := ⟨-1, by simp, by simp [deckU, Zunit_add_one_u], by simp [deckU]; ring⟩
  comm := hD.commU

lemma isDeck_deckV (hD : DeckEquivariant PhiInv) : IsDeck PhiInv deckV 0 1 where
  shift2 X := by simp [deckV]
  shift3 X := by simp [deckV]
  gauge X := ⟨deckFactor (X 2) (X 3), deckFactor_unit _ _, by simp [deckV, Zunit_add_one_v],
    by simp [deckV]⟩
  comm := hD.commV

/-- **Every shift `(m, n) ∈ ℤ²` is realised by a deck map.** -/
theorem exists_isDeck (hD : DeckEquivariant PhiInv) (m n : ℤ) :
    ∃ T : E4 → E4, IsDeck PhiInv T m n := by
  have hU := isDeck_deckU hD
  have hV := isDeck_deckV hD
  have hUi := hU.inv deckU_deckUinv deckUinv_deckU
  have hVi := hV.inv deckV_deckVinv deckVinv_deckV
  have hm : ∀ m : ℤ, ∃ T, IsDeck PhiInv T m 0 := by
    intro m
    induction m using Int.induction_on with
    | zero => exact ⟨id, isDeck_id⟩
    | succ i ih =>
      obtain ⟨T, hT⟩ := ih
      exact ⟨_, (hU.comp hT).of_eq (by ring) (by ring)⟩
    | pred i ih =>
      obtain ⟨T, hT⟩ := ih
      exact ⟨_, (hUi.comp hT).of_eq (by ring) (by ring)⟩
  have hn : ∀ n : ℤ, ∃ T, IsDeck PhiInv T 0 n := by
    intro n
    induction n using Int.induction_on with
    | zero => exact ⟨id, isDeck_id⟩
    | succ i ih =>
      obtain ⟨T, hT⟩ := ih
      exact ⟨_, (hV.comp hT).of_eq (by ring) (by ring)⟩
    | pred i ih =>
      obtain ⟨T, hT⟩ := ih
      exact ⟨_, (hVi.comp hT).of_eq (by ring) (by ring)⟩
  obtain ⟨T, hT⟩ := hm m
  obtain ⟨S, hS⟩ := hn n
  exact ⟨_, (hT.comp hS).of_eq (by ring) (by ring)⟩

lemma IsDeck.pE_eq {T : E4 → E4} {m n : ℤ} (hT : IsDeck PhiInv T m n) (X : E4) :
    Bundle.pE (T X) = Bundle.pE X := by
  obtain ⟨c, hc, -, hw⟩ := hT.gauge X
  have hn : ‖c‖ = 1 := by
    have h := congrArg Complex.re hc
    rw [conj_mul'] at h
    have h' : ‖c‖ ^ 2 = 1 := by exact_mod_cast h
    nlinarith [norm_nonneg c]
  rw [Handle.pE_eq, Handle.pE_eq, hw, norm_mul, norm_pow, hn, one_pow, one_mul]

/-! ### Injectivity of `Ncoord` modulo deck and gauge -/

/-- **`Ncoord A = μ · Ncoord B` forces `A = T B`** for a deck map `T`. -/
theorem gauge_imp_deck (hD : DeckEquivariant PhiInv) {A B : E4} {μ : ℂ} (hμ : conj μ * μ = 1)
    (h : Ncoord A = (μ • (Ncoord B).1, μ ^ 3 * (Ncoord B).2)) :
    ∃ T : E4 → E4, ∃ m n : ℤ, IsDeck PhiInv T m n ∧ A = T B := by
  rw [Ncoord_eq, Ncoord_eq] at h
  have hZ : Zunit (A 2) (A 3) = μ • Zunit (B 2) (B 3) := congrArg Prod.fst h
  have hw : wL A = μ ^ 3 * wL B := congrArg Prod.snd h
  obtain ⟨m, n, hm, hn⟩ := Zunit_proj (unit_ne_zero hμ) hZ
  obtain ⟨T, hT⟩ := exists_isDeck hD (-m) (-n)
  have h2 : T B 2 = A 2 := by rw [hT.shift2, hm]; push_cast; ring
  have h3 : T B 3 = A 3 := by rw [hT.shift3, hn]; push_cast; ring
  obtain ⟨c, -, hcZ, hcw⟩ := hT.gauge B
  rw [h2, h3, hZ] at hcZ
  have hc : μ = c := smul_left_injective ℂ (Zunit_ne_zero (B 2) (B 3)) hcZ
  refine ⟨T, -m, -n, hT, E4_ext3 ?_ h2.symm h3.symm⟩
  rw [hw, hcw, hc]

/-- **A deck map relating two points of the band `(1/8, 5/24)²` fixes them**: `m = n = 0` and
then the gauge factor is `1`. -/
theorem IsDeck.eq_of_band {T : E4 → E4} {m n : ℤ} (hT : IsDeck PhiInv T m n) {Y Y' : E4}
    (h : Y = T Y') (hY2 : Y 2 ∈ Ioo (1 / 8 : ℝ) (5 / 24)) (hY2' : Y' 2 ∈ Ioo (1 / 8 : ℝ) (5 / 24))
    (hY3 : Y 3 ∈ Ioo (1 / 8 : ℝ) (5 / 24)) (hY3' : Y' 3 ∈ Ioo (1 / 8 : ℝ) (5 / 24)) :
    Y = Y' := by
  have e2 := hT.shift2 Y'
  have e3 := hT.shift3 Y'
  rw [← h] at e2 e3
  have hm : m = 0 := by
    have a : (m : ℝ) < 1 := by linarith [hY2.2, hY2'.1]
    have b : (-1 : ℝ) < m := by linarith [hY2.1, hY2'.2]
    have a' : m < 1 := by exact_mod_cast a
    have b' : -1 < m := by exact_mod_cast b
    omega
  have hn : n = 0 := by
    have a : (n : ℝ) < 1 := by linarith [hY3.2, hY3'.1]
    have b : (-1 : ℝ) < n := by linarith [hY3.1, hY3'.2]
    have a' : n < 1 := by exact_mod_cast a
    have b' : -1 < n := by exact_mod_cast b
    omega
  subst hm hn
  simp only [Int.cast_zero, add_zero] at e2 e3
  obtain ⟨c, -, hcZ, hcw⟩ := hT.gauge Y'
  rw [← h, e2, e3] at hcZ
  rw [← h] at hcw
  have hc : (1 : ℂ) = c := smul_left_injective ℂ (Zunit_ne_zero (Y' 2) (Y' 3))
    (by simpa using hcZ)
  refine E4_ext3 ?_ e2 e3
  rw [hcw, ← hc, one_pow, one_mul]

end SymplecticPacking.Embed
