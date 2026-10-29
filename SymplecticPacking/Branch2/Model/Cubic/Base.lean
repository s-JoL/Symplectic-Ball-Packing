import SymplecticPacking.Branch2.Model.Data

/-!
# Valid cubic data, and the comparison isotopy of the data

`VCubic` bundles `D : CubicData` with `D.Valid`; the model-stage files
(`Branch2/Model/Cubic/*`) are written for `P : VCubic`, with the lemmas `P.g_pos`, `P.h_lt_dn`,
`P.Hstar_ge`, … provided below. The comparison
isotopy `q̂_t` is `Qhat.qhat P.path` (`Qhat.Cubic.qhatP`).
-/

noncomputable section

namespace SymplecticPacking.Branch2

open Set
open scoped Real ContDiff

/-- Cubic data together with its validity. -/
structure VCubic extends CubicData where
  valid : CubicData.Valid toCubicData

namespace VCubic

variable (P : VCubic)

lemma a_lt_h {i : ℕ} (h1 : 1 ≤ i) (hk : i ≤ P.k) : P.a i < P.h := P.valid.a_lt_h i h1 hk
lemma h_pos : 0 < P.h := P.valid.h_pos
lemma h_lt_dn : P.h < P.dn := P.valid.h_lt_dn
lemma dn_lt_third : P.dn < 1 / 3 := P.valid.dn_lt_third
lemma h_lt_third : P.h < 1 / 3 := P.valid.h_lt_third
lemma g_pos : 0 < P.g := P.valid.g_pos
lemma muh_pos : 0 < P.muh := P.valid.muh_pos
lemma K_smooth : ContDiff ℝ ∞ P.K := P.valid.K_smooth
lemma Hstar_ge {p : ℝ} (hp : p ≤ P.h) : 15 * P.g / 16 ≤ P.Hstar p := P.valid.Hstar_ge hp
lemma hi_gt_pos_part (i : ℕ) (p : ℝ) : max (P.a i - p) 0 < P.hi i p :=
  P.valid.hi_gt_pos_part i p
lemma sum_hi_le (p : ℝ) :
    ∑ i ∈ Finset.Icc 1 P.k, P.hi i p ≤ ∑ i ∈ Finset.Icc 1 P.k, max (P.a i - p) 0 + P.g / 32 :=
  P.valid.sum_hi_le p
theorem residual_ge {I p' : ℝ} (h1 : 31 * P.g / 32 ≤ P.K I - P.F p') :
    7 * P.g / 8 ≤ P.K I - P.J p' - ∑ i ∈ Finset.Icc 1 P.k, P.hi i p' :=
  P.valid.residual_ge h1
lemma deltaStrip_pos {i : ℕ} (h1 : 1 ≤ i) (hk : i ≤ P.k) : 0 < P.deltaStrip i :=
  P.valid.deltaStrip_pos h1 hk

/-- `H*(q) = H*(p) − 9(q − p)`. -/
lemma Hstar_sub (p q : ℝ) : P.Hstar q = P.Hstar p - 9 * (q - p) := by
  unfold CubicData.Hstar CubicData.Hb; ring

/-- `H*(h) ≥ 15g/16`. -/
lemma Hstar_h_ge : 15 * P.g / 16 ≤ P.Hstar P.h := P.Hstar_ge le_rfl

end VCubic

end SymplecticPacking.Branch2

namespace SymplecticPacking.Qhat.Cubic

open SymplecticPacking.Branch2
open scoped Real ContDiff

variable (P : VCubic)

/-- The comparison path of the data. -/
def pathData : PathData := P.path

theorem ordinaryPath : OrdinaryPath (pathData P) := P.valid.path_ok

lemma pathData_h : (pathData P).h = P.h := P.valid.path_h

/-- The whole-disk isotopy `q̂_t`. -/
def qhatP : ℝ → ℂ → ℂ := qhat (pathData P)

/-- Its inverse. -/
def qhatInvP : ℝ → ℂ → ℂ := qhatInv (pathData P)

/-- The Hamiltonian `Q_t`. -/
def QhamP : ℝ → ℂ → ℝ := Qham (pathData P)

/-- The support area `P_supp`. -/
def Psupp : ℝ := (pathData P).Psupp

theorem Psupp_lt : Psupp P < P.h := by
  have := (ordinaryPath P).Psupp_lt_h
  rw [pathData_h] at this
  exact this

theorem qhatP_spec :
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => qhatP P p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => qhatInvP P p.1 p.2) ∧
    ContDiff ℝ ∞ (fun p : ℝ × ℂ => QhamP P p.1 p.2) ∧
    (∀ t z, LinearMap.det (fderiv ℝ (qhatP P t) z : ℂ →ₗ[ℝ] ℂ) = 1) ∧
    (∀ t, Function.Bijective (qhatP P t)) ∧
    Psupp P < P.h ∧
    (∀ t z, Psupp P < π * ‖z‖ ^ 2 → qhatP P t z = z) ∧
    (∀ t y, Psupp P < π * ‖y‖ ^ 2 → QhamP P t y = 0) ∧
    (∀ t y, (t ≤ 0 ∨ 1 ≤ t) → QhamP P t y = 0) ∧
    (∀ t z, HasDerivAt (fun s => qhatP P s z) (hamVF2 (QhamP P t) (qhatP P t z)) t) ∧
    (∀ t z v, omega2 (hamVF2 (QhamP P t) (qhatP P t z)) v =
      -fderiv ℝ (QhamP P t) (qhatP P t z) v) ∧
    qhatP P 0 = id ∧
    (∀ t z, qhatInvP P t (qhatP P t z) = z) ∧
    (∀ t y, qhatP P t (qhatInvP P t y) = y) := by
  have hD := ordinaryPath P
  obtain ⟨h1, h2, h3, h4, h5, -, h7, h8, h9, h10, h11, h12, -⟩ := qhat_interface hD
  exact ⟨h1, h2, h3, h4, h5, Psupp_lt P, h7, h8, h9, h10, h11, h12, qhatInv_qhat hD,
    qhat_qhatInv hD⟩

/-- **`eq:shd4-comparison`** for the data. -/
theorem full_comparison {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ P.h) :
    31 * P.g / 32 ≤ P.K (π * ‖z‖ ^ 2) - P.F (π * ‖qhatP P 1 z‖ ^ 2) :=
  P.valid.comparison z hz

end SymplecticPacking.Qhat.Cubic
