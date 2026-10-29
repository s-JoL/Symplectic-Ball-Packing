import SymplecticPacking.Qhat.FivePath
import SymplecticPacking.Qhat.Ham

/-!
# The concrete comparison isotopy

`sec:pln`: connecting the concrete five-segment path of `sec:pln-five` (`ordPath P`,
`FivePath.lean`) with the generic construction of `sec:pln-flow`–`sec:pln-ham` (`Flow`, `Normal`, `Ham`).

* `pathData P` bundles the concrete data; `ordinaryPath P` verifies the interface
  `OrdinaryPath` field by field from `lem:pln-five-segment`, `lem:pln-data`,
  `lem:pll-source-order`.
* `qhatP P` is the concrete whole-disk isotopy.
* `endpoint_comparison` is the `sec:pll` estimate (5) for the endpoint `𝔢_1`, discharged via
  `Inner.comparison_five` and `qinner_one` (`q^in_1 = C ∘ f`); `full_comparison` is
  `eq:pll-full-comparison` of `thm:pln-isotopy`.
-/

noncomputable section

namespace SymplecticPacking.Qhat

open Set
open scoped ContDiff Real

variable (P : Params)

/-- The concrete `sec:pln-five` data: `𝔢 = ordPath P`, `γ = gammaDet P`, `h`, `e = e_q`, `p†`, `P_supp`,
`c = c_new`. -/
def pathData : PathData where
  path := ordPath P
  gam := gammaDet P
  h := P.h
  e := P.eq_
  pdag := pdag P
  Psupp := Psupp P
  c := cnew P

/-- **Interface check.** The concrete five-segment path is an ordinary path. -/
theorem ordinaryPath : OrdinaryPath (pathData P) where
  e_pos := P.eq_pos
  four_e_lt_h := by
    show 4 * P.eq_ < P.h
    linarith [P.eq_le_h, P.h_pos]
  pplus_lt_pdag := (pdag_bounds P).1
  Psupp_lt_h := Psupp_lt P
  c_pos := (cnew_pos P).1
  smooth := ordPath_smooth P
  eq_id := fun _ ht z _ => ordPath_of_nonpos P ht z
  eq_one := fun _ ht z _ => ordPath_eq_one P ht z
  injOn := ordPath_injOn P
  det := fun t _ hz => ordPath_det P t hz
  gam_smooth := gammaDet_contDiff P
  gam_ge := fun t => (gammaDet_bounds P t).1
  gam_one := (gammaDet_bounds P 0).2.2.2
  image := fun t _ hz => ordPath_image_area P t hz

/-- The concrete whole-disk isotopy `q̂_t`. -/
def qhatP : ℝ → ℂ → ℂ := qhat (pathData P)

/-- Its inverse `q̂_t⁻¹`. -/
def qhatInvP : ℝ → ℂ → ℂ := qhatInv (pathData P)

/-- The concrete Hamiltonian `Q_t`. -/
def QhamP : ℝ → ℂ → ℝ := Qham (pathData P)

/-- **`thm:pln-isotopy` + `prop:pln-hamiltonian` (concrete).** Joint smoothness of `q̂`, `q̂⁻¹`, `Q`;
`det Dq̂_t = 1`; bijectivity; `P_supp < h`; `q̂_t = id` and `Q_t = 0` on `{π|z|² > P_supp}`;
`Q_t = 0` for `t ∉ (0,1)`; `∂_t q̂_t = X_{Q_t} ∘ q̂_t` with `ι_{X_Q}ω₂ = -dQ`; `q̂_0 = id`;
`q̂_t⁻¹` is a two-sided inverse. -/
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
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩ := qhat_interface hD
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, qhatInv_qhat hD, qhat_qhatInv hD⟩

/-- `h - 4e ≤ p†`. -/
lemma h_sub_four_e_le_pdag : P.h - 4 * P.eq_ ≤ pdag P := by
  have := (pdag_bounds P).1
  have := P.eq_pos
  unfold Params.pplus at *
  linarith

/-- **Estimate (5) for the endpoint `𝔢_1`**, discharged from `sec:pll` (`Inner.comparison_five`). -/
theorem endpoint_comparison {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ P.h - 4 * P.eq_) :
    P.Rcal (π * ‖(pathData P).path 1 z‖ ^ 2) < π * ‖z‖ ^ 2 + 13 * P.eq_ / 24 := by
  have hz' := hz.trans (h_sub_four_e_le_pdag P)
  have hdom := (qinner_dom P ⟨zero_le_one, le_rfl⟩ hz').2
  rw [lam_one, one_mul, fs_eq_finner] at hdom
  show P.Rcal (π * ‖ordPath P 1 z‖ ^ 2) < _
  rw [ordPath_of_one_le P le_rfl, qinner_one P hz']
  exact (Inner.comparison_five P z hdom.le).2

/-- **`eq:pll-full-comparison`.** On the whole closed disk `π|z|² ≤ h`, with `I = π|z|²`:
`K(I) - F(π|q̂_1 z|²) ≥ 31g/32`. -/
theorem full_comparison {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ P.h) :
    31 * P.g / 32 ≤ P.K (π * ‖z‖ ^ 2) - P.F (π * ‖qhatP P 1 z‖ ^ 2) :=
  K_sub_F_q_ge (ordinaryPath P) P rfl rfl (fun _ hz => endpoint_comparison P hz) hz

end SymplecticPacking.Qhat
