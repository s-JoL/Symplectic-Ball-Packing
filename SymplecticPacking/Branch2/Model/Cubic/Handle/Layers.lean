import SymplecticPacking.Handle.Layers
import SymplecticPacking.Branch2.Model.Cubic.Handle.Twist

/-!
# The residual, the layer intervals and the final coefficient

For valid cubic data `P : Branch2.VCubic` (namespace `SymplecticPacking.Handle.Cubic`), with
per-ball `a_i`, `h_i`, `ρ̄_i`, `δ_i`, `ρ̂_i` and a general smooth `K`, so that `J = K - H*` is
nonlinear.

`sec:shd-four` (`def:shd4-scalars`, `lem:shd4-budget`, `def:shd4-frame`, `lem:shd4-Gf`):
the residual `R*`, the layer intervals and the final coefficient `G_f`.

The scalar data `μ_h`, `h_i`, `J` and their estimates (`def:shd4-scalars`, `lem:shd4-budget`) are
`CubicData.muh`, `CubicData.hi i`, `CubicData.J`, `VCubic.Hstar_ge`, `VCubic.hi_gt_pos_part`,
`VCubic.sum_hi_le`, `VCubic.residual_ge` (`Branch2/Model/Data.lean`,
`Cubic/Base.lean`); sums `∑_{i=1}^k` are over `Finset.Icc 1 k`.

* `Rstar P w = K(p(q⁻¹w)) − J(p(w)) − ∑ h_i(p(w))` with `q = q̂₁`; `Rstar_ge`: `R* ≥ 7g/8` on
  `D̄(h)`, from the comparison `Valid.comparison` at the source point `z = q⁻¹(w)`.
* `layerLeft j`, `layerRight j`, `rhoLayer j` for `1 ≤ j ≤ N_ℓ = k + 1`; `Gf P s w`;
  `Gf_mono`, `Gf_low`, `Gf_up`, `Gf_layer`.
-/

noncomputable section

namespace SymplecticPacking.Handle.Cubic

open Set Filter Topology
open SymplecticPacking.Bundle (stepA u0 u1)
open SymplecticPacking.Qhat.Cubic (qhatP qhatInvP Psupp)
open scoped ContDiff Real

variable (P : Branch2.VCubic)

/-! ### Disk preservation -/

lemma qhatP_mem_closedDisk {c : ℝ} (hc : Psupp P ≤ c) (τ : ℝ) {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ c) :
    π * ‖qhatP P τ z‖ ^ 2 ≤ c := by
  have h := Qhat.qhat_disk (Qhat.Cubic.ordinaryPath P) (P := c) hc τ
  have : qhatP P τ z ∈ Qhat.qhat (Qhat.Cubic.pathData P) τ '' Qhat.closedAreaDisk c := ⟨z, hz, rfl⟩
  rw [h] at this; exact this

lemma qhatInvP_mem_closedDisk {c : ℝ} (hc : Psupp P ≤ c) (τ : ℝ) {w : ℂ} (hw : π * ‖w‖ ^ 2 ≤ c) :
    π * ‖qhatInvP P τ w‖ ^ 2 ≤ c := by
  have h := Qhat.qhat_disk (Qhat.Cubic.ordinaryPath P) (P := c) hc τ
  have hw' : w ∈ Qhat.qhat (Qhat.Cubic.pathData P) τ '' Qhat.closedAreaDisk c := by rw [h]; exact hw
  obtain ⟨z, hz, rfl⟩ := hw'
  have e : qhatInvP P τ (Qhat.qhat (Qhat.Cubic.pathData P) τ z) = z := qhatInvP_qhatP P τ z
  rw [e]; exact hz

lemma qhatP_mem_openDisk {c : ℝ} (hc : Psupp P < c) (τ : ℝ) {z : ℂ} (hz : π * ‖z‖ ^ 2 < c) :
    π * ‖qhatP P τ z‖ ^ 2 < c := by
  have h := Qhat.qhat_openDisk (Qhat.Cubic.ordinaryPath P) (P := c) hc τ
  have : qhatP P τ z ∈ Qhat.qhat (Qhat.Cubic.pathData P) τ '' Qhat.areaDisk c := ⟨z, hz, rfl⟩
  rw [h] at this; exact this

lemma qhatInvP_mem_openDisk {c : ℝ} (hc : Psupp P < c) (τ : ℝ) {w : ℂ} (hw : π * ‖w‖ ^ 2 < c) :
    π * ‖qhatInvP P τ w‖ ^ 2 < c := by
  have h := Qhat.qhat_openDisk (Qhat.Cubic.ordinaryPath P) (P := c) hc τ
  have hw' : w ∈ Qhat.qhat (Qhat.Cubic.pathData P) τ '' Qhat.areaDisk c := by rw [h]; exact hw
  obtain ⟨z, hz, rfl⟩ := hw'
  have e : qhatInvP P τ (Qhat.qhat (Qhat.Cubic.pathData P) τ z) = z := qhatInvP_qhatP P τ z
  rw [e]; exact hz

lemma Psupp_lt_h : Psupp P < P.h := Qhat.Cubic.Psupp_lt P

/-! ### The residual (`def:shd4-scalars`, `lem:shd4-budget`) -/

/-- **The residual** `R*(w) = K(p(q⁻¹ w)) − J(p(w)) − ∑_{i=1}^k h_i(p(w))`, `q = q̂₁`. -/
def Rstar (w : ℂ) : ℝ :=
  P.K (π * ‖qhatInvP P 1 w‖ ^ 2) - P.J (π * ‖w‖ ^ 2) -
    ∑ i ∈ Finset.Icc 1 P.k, P.hi i (π * ‖w‖ ^ 2)

/-- **Residual estimate** (`lem:shd4-budget`): `R* ≥ 7g/8` on `D̄(h)`. -/
theorem Rstar_ge {w : ℂ} (hw : π * ‖w‖ ^ 2 ≤ P.h) : 7 * P.g / 8 ≤ Rstar P w := by
  have hz := qhatInvP_mem_closedDisk P (Psupp_lt_h P).le 1 hw
  have hc := Qhat.Cubic.full_comparison P hz
  rw [qhatP_qhatInvP] at hc
  have := P.residual_ge hc
  rw [Rstar]; linarith

lemma contDiff_hi (i : ℕ) : ContDiff ℝ ∞ (P.hi i) := by
  have hq : ContDiff ℝ ∞ (fun p : ℝ => (P.a i - p) ^ 2 + P.muh ^ 2) := by fun_prop
  have hs := hq.sqrt (fun p => by have := P.muh_pos; positivity)
  exact ((contDiff_const.sub contDiff_id).add hs).div_const 2

lemma hi_pos (i : ℕ) (p : ℝ) : 0 < P.hi i p :=
  lt_of_le_of_lt (le_max_right _ _) (P.hi_gt_pos_part i p)

lemma contDiff_K : ContDiff ℝ ∞ P.K := P.K_smooth
lemma contDiff_Hstar : ContDiff ℝ ∞ P.Hstar := by
  unfold Branch2.CubicData.Hstar Branch2.CubicData.Hb; fun_prop
lemma contDiff_J : ContDiff ℝ ∞ P.J := (contDiff_K P).sub (contDiff_Hstar P)

theorem contDiff_Rstar : ContDiff ℝ ∞ (Rstar P) := by
  have hp := contDiff_fibreArea
  unfold Rstar
  refine ((contDiff_K P).comp (hp.comp (contDiff_qhatInvP P 1))).sub
    ((contDiff_J P).comp hp) |>.sub ?_
  exact ContDiff.sum fun i _ => (contDiff_hi P i).comp hp

/-! ### Layer intervals (`def:shd4-frame`) -/

/-- `N_ℓ = k + 1` layers: `k` toric ones and the residual one `* = N_ℓ`. -/
def Nlayers : ℕ := P.k + 1

/-- `ℓ_s = (u₁ − u₀)/N_ℓ`. -/
def ells : ℝ := (u1 - u0) / (Nlayers P)

/-- `left_j = u₀ + (j − 1)ℓ_s + ℓ_s/4`. -/
def layerLeft (j : ℕ) : ℝ := u0 + ((j : ℝ) - 1) * (ells P) + (ells P) / 4

/-- `right_j = u₀ + (j − 1)ℓ_s + 3ℓ_s/4`. -/
def layerRight (j : ℕ) : ℝ := u0 + ((j : ℝ) - 1) * (ells P) + 3 * (ells P) / 4

/-- `ρ_j(s) = S((s − left_j)/(right_j − left_j))`. -/
def rhoLayer (j : ℕ) (s : ℝ) : ℝ :=
  flatStep ((s - (layerLeft P) j) / ((layerRight P) j - (layerLeft P) j))

lemma Nlayers_pos : (0 : ℝ) < (Nlayers P) := by unfold Nlayers; positivity

lemma ells_pos : 0 < (ells P) := div_pos (by norm_num [u0, u1]) (Nlayers_pos P)

lemma layerRight_sub_left (j : ℕ) : (layerRight P) j - (layerLeft P) j = (ells P) / 2 := by
  unfold layerRight layerLeft; ring

lemma rhoLayer_eq_zero {j : ℕ} {s : ℝ} (hs : s ≤ (layerLeft P) j) : (rhoLayer P) j s = 0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith)
    (by rw [layerRight_sub_left]; linarith [(ells_pos P)]))

lemma rhoLayer_eq_one {j : ℕ} {s : ℝ} (hs : (layerRight P) j ≤ s) : (rhoLayer P) j s = 1 :=
  Real.smoothTransition.one_of_one_le (by
    rw [le_div_iff₀ (by rw [layerRight_sub_left]; linarith [(ells_pos P)])]; linarith)

lemma monotone_rhoLayer (j : ℕ) : Monotone ((rhoLayer P) j) := fun a b hab =>
  Real.smoothTransition.monotone (div_le_div_of_nonneg_right (by linarith)
    (by rw [layerRight_sub_left]; linarith [(ells_pos P)]))

lemma contDiff_rhoLayer (j : ℕ) : ContDiff ℝ ∞ ((rhoLayer P) j) :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)

/-- The layers are ordered: `right_j < left_i` for `j < i`. -/
lemma layerRight_lt_left {i j : ℕ} (h : j < i) : (layerRight P) j < (layerLeft P) i := by
  have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
  have := (ells_pos P)
  unfold layerRight layerLeft; nlinarith

lemma layerLeft_mono {i j : ℕ} (h : j ≤ i) : (layerLeft P) j ≤ (layerLeft P) i := by
  have : (j : ℝ) ≤ i := by exact_mod_cast h
  have := (ells_pos P)
  unfold layerLeft; nlinarith

lemma layerRight_mono {i j : ℕ} (h : j ≤ i) : (layerRight P) j ≤ (layerRight P) i := by
  have : (j : ℝ) ≤ i := by exact_mod_cast h
  have := (ells_pos P)
  unfold layerRight; nlinarith

/-- The lower collar: `u₀ < left_1`. -/
lemma u0_lt_layerLeft_one : u0 < (layerLeft P) 1 := by
  unfold layerLeft; simp; linarith [(ells_pos P)]

/-- The upper collar: `right_* < u₁`. -/
lemma layerRight_N_lt_u1 : (layerRight P) (Nlayers P) < u1 := by
  have h := (Nlayers_pos P)
  have e : (((Nlayers P) : ℝ) - 1) * (ells P) + 3 * (ells P) / 4 = (u1 - u0) - (ells P) / 4 := by
    unfold ells; field_simp; ring
  unfold layerRight; rw [add_assoc, e]; linarith [(ells_pos P)]

/-! ### The final coefficient (`lem:shd4-Gf`) -/

/-- **`G_f(s, w) = J(p) + ∑_{i=1}^k ρ_i(s) h_i(p) + ρ_*(s) R*(w)`**, `p = p(w)`. -/
def Gf (s : ℝ) (w : ℂ) : ℝ :=
  P.J (π * ‖w‖ ^ 2) + ∑ i ∈ Finset.Icc 1 P.k, (rhoLayer P) i s * P.hi i (π * ‖w‖ ^ 2) +
    (rhoLayer P) (Nlayers P) s * Rstar P w

/-- The toric part below layer `i`: `a_i = J + ∑_{j<i} h_j`. -/
def aLayer (i : ℕ) (p : ℝ) : ℝ := P.J p + ∑ j ∈ Finset.Ico 1 i, P.hi j p

theorem contDiff_Gf : ContDiff ℝ ∞ (fun z : ℝ × ℂ => Gf P z.1 z.2) := by
  have hp : ContDiff ℝ ∞ (fun z : ℝ × ℂ => π * ‖z.2‖ ^ 2) := contDiff_fibreArea.comp contDiff_snd
  unfold Gf
  refine (((contDiff_J P).comp hp).add (ContDiff.sum fun i _ =>
    ((contDiff_rhoLayer P i).comp contDiff_fst).mul ((contDiff_hi P i).comp hp))).add ?_
  exact ((contDiff_rhoLayer P _).comp contDiff_fst).mul ((contDiff_Rstar P).comp contDiff_snd)

lemma hasDerivAt_rhoLayer (j : ℕ) (s : ℝ) :
    HasDerivAt ((rhoLayer P) j) (deriv ((rhoLayer P) j) s) s :=
  ((contDiff_rhoLayer P j).differentiable (by simp) s).hasDerivAt

/-- `∂_s G_f = ∑_i ρ_i' h_i + ρ_*' R*`. -/
theorem hasDerivAt_Gf (s : ℝ) (w : ℂ) :
    HasDerivAt (fun σ => Gf P σ w)
      (∑ i ∈ Finset.Icc 1 P.k, deriv ((rhoLayer P) i) s * P.hi i (π * ‖w‖ ^ 2) +
        deriv ((rhoLayer P) (Nlayers P)) s * Rstar P w) s := by
  have h1 := HasDerivAt.sum (u := Finset.Icc 1 P.k)
    (A := fun i σ => (rhoLayer P) i σ * P.hi i (π * ‖w‖ ^ 2))
    (A' := fun i => deriv ((rhoLayer P) i) s * P.hi i (π * ‖w‖ ^ 2))
    (x := s) fun i _ => (hasDerivAt_rhoLayer P i s).mul_const _
  have h2 := (hasDerivAt_rhoLayer P (Nlayers P) s).mul_const (Rstar P w)
  have := ((hasDerivAt_const s (P.J (π * ‖w‖ ^ 2))).add h1).add h2
  simp only [zero_add] at this
  convert this using 1
  funext σ; simp [Gf, Finset.sum_apply]

/-- **`lem:shd4-Gf`(a)**: `∂_s G_f ≥ 0` wherever `R* ≥ 0`. -/
theorem Gf_mono {w : ℂ} (hR : 0 ≤ Rstar P w) (s : ℝ) : 0 ≤ deriv (fun σ => Gf P σ w) s := by
  rw [(hasDerivAt_Gf P s w).deriv]
  refine add_nonneg (Finset.sum_nonneg fun i _ => ?_) ?_
  · exact mul_nonneg ((monotone_rhoLayer P i).deriv_nonneg) (hi_pos P i _).le
  · exact mul_nonneg ((monotone_rhoLayer P _).deriv_nonneg) hR

/-- **`lem:shd4-Gf`(b), lower end**: `G_f = J ∘ p` for `s ≤ left_1`. -/
theorem Gf_low {s : ℝ} (hs : s ≤ (layerLeft P) 1) (w : ℂ) : Gf P s w = P.J (π * ‖w‖ ^ 2) := by
  have h0 : ∀ j, 1 ≤ j → (rhoLayer P) j s = 0 := fun j hj =>
    (rhoLayer_eq_zero P) (hs.trans ((layerLeft_mono P) hj))
  rw [Gf, Finset.sum_eq_zero fun i hi => by rw [h0 i (Finset.mem_Icc.mp hi).1, zero_mul],
    h0 _ (by unfold Nlayers; omega), zero_mul, add_zero, add_zero]

/-- **`lem:shd4-Gf`(b), upper end**: `G_f = K ∘ p ∘ q⁻¹` for `s ≥ right_*`. -/
theorem Gf_up {s : ℝ} (hs : (layerRight P) (Nlayers P) ≤ s) (w : ℂ) :
    Gf P s w = P.K (π * ‖qhatInvP P 1 w‖ ^ 2) := by
  have h1 : ∀ j, j ≤ (Nlayers P) → (rhoLayer P) j s = 1 := fun j hj =>
    (rhoLayer_eq_one P) (((layerRight_mono P) hj).trans hs)
  rw [Gf, Finset.sum_congr rfl fun i hi => by
      rw [h1 i (by have := (Finset.mem_Icc.mp hi).2; unfold Nlayers; omega), one_mul],
    h1 _ le_rfl, one_mul, Rstar]
  ring

/-- **`lem:shd4-Gf`(c)**: on the `i`-th layer interval, `1 ≤ i ≤ k`,
`G_f = a_i(p) + ρ_i(s) h_i(p)`, `a_i = J + ∑_{j<i} h_j`; in particular `G_f` is toric there. -/
theorem Gf_layer {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {s : ℝ}
    (hs : s ∈ Ioo ((layerLeft P) i) ((layerRight P) i)) (w : ℂ) :
    Gf P s w = (aLayer P) i (π * ‖w‖ ^ 2) + (rhoLayer P) i s * P.hi i (π * ‖w‖ ^ 2) := by
  set p := π * ‖w‖ ^ 2
  have hlow : ∀ j, j < i → (rhoLayer P) j s = 1 := fun j hj =>
    (rhoLayer_eq_one P) (((layerRight_lt_left P) hj).le.trans hs.1.le)
  have hup : ∀ j, i < j → (rhoLayer P) j s = 0 := fun j hj =>
    (rhoLayer_eq_zero P) (hs.2.le.trans ((layerRight_lt_left P) hj).le)
  set f : ℕ → ℝ := fun j => rhoLayer P j s * P.hi j p
  have hsplit : ∑ j ∈ Finset.Icc 1 P.k, f j =
      ∑ j ∈ Finset.Ico 1 i, f j + f i + ∑ j ∈ Finset.Ico (i + 1) (P.k + 1), f j := by
    rw [← Finset.Ico_add_one_right_eq_Icc,
      ← Finset.sum_Ico_consecutive f hi1 (show i ≤ P.k + 1 by omega),
      Finset.sum_eq_sum_Ico_succ_bot (show i < P.k + 1 by omega)]
    ring
  have h1 : ∑ j ∈ Finset.Ico 1 i, f j = ∑ j ∈ Finset.Ico 1 i, P.hi j p :=
    Finset.sum_congr rfl fun j hj => by
      simp only [f]; rw [hlow j (Finset.mem_Ico.mp hj).2, one_mul]
  have h2 : ∑ j ∈ Finset.Ico (i + 1) (P.k + 1), f j = 0 :=
    Finset.sum_eq_zero fun j hj => by
      simp only [f]; rw [hup j (by have := (Finset.mem_Ico.mp hj).1; omega), zero_mul]
  have h3 : rhoLayer P (Nlayers P) s = 0 := hup _ (by unfold Nlayers; omega)
  show P.J p + ∑ j ∈ Finset.Icc 1 P.k, f j + rhoLayer P (Nlayers P) s * Rstar P w = _
  rw [hsplit, h1, h2, h3, aLayer]
  simp only [f]
  ring

end SymplecticPacking.Handle.Cubic
