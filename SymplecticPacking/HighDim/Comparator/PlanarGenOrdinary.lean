import SymplecticPacking.HighDim.Comparator.PlanarGen

/-!
# The five-segment path of `planarGen` is ordinary (`RealiseGen.planarGen_ordinary`)

`lem:pln-five-segment` uniformly in `y`.

Part 1 (`FiveData`): the generic five-segment path (shrink by `c`, translate to `b`,
linear deformation `𝐌_σ`, inner deformation `q_σ`, convex expansion from `b`) built from an
abstract inner family `q_σ` with **abstract constants** `c, B₃, B*, R_q, R_supp` (in place of the
closed formulas of `Branch2.Planar.FamData`, which depend on `|b|`); the constants only enter
through the inequalities of `FiveData.Hyp`. Proofs follow `Branch2/Planar/FiveGeneric.lean`.

Part 2: the instance `Input.fiveData D y` (inner family `q_{y,σ} = D.qin y σ`, uniform constants
of `PlanarGen.lean` §6) and the reduction of `Qhat.OrdinaryPath (D.pathData y)` to
`FiveData.Hyp (D.fiveData y)`.
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen

open Filter Topology Set Complex
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff Real

/-- The data of an abstract inner family with abstract five-segment constants. -/
structure FiveData where
  q : ℝ → ℂ → ℂ
  b : ℂ
  A11 : ℝ
  A22 : ℝ
  h : ℝ
  pdag : ℝ
  c : ℝ
  B3 : ℝ
  Bstar : ℝ
  Rq : ℝ
  Rsupp : ℝ

namespace FiveData

variable (D : FiveData)

/-- `𝐀₀ = diag(A₁₁, A₂₂)`. -/
def A0 : ℂ →L[ℝ] ℂ :=
  ofRealCLM.comp (D.A11 • reCLM) + (ofRealCLM.comp (D.A22 • imCLM)).smulRight I

lemma A0_apply (z : ℂ) : D.A0 z = ((D.A11 * z.re : ℝ) : ℂ) + ((D.A22 * z.im : ℝ) : ℂ) * I := by
  simp [A0]

/-- The source disk `D(p†)`. -/
def srcDisk : Set ℂ := {z | π * ‖z‖ ^ 2 < D.pdag}

/-- `r_b = |b|`. -/
def rb : ℝ := ‖D.b‖

/-- `R† = √(p†/π)`. -/
def Rdag : ℝ := √(D.pdag / π)

/-- `c` (named as in `FiveGeneric`). -/
def cnew : ℝ := D.c

/-- `P_supp = π R_supp²`. -/
def Psupp : ℝ := π * D.Rsupp ^ 2

/-- `𝐌_σ = Rot_{πσ} diag(|A₁₁|^σ, |A₂₂|^σ)`. -/
def Msig (σ : ℝ) (z : ℂ) : ℂ :=
  Inner.Rot (π * σ) (((|D.A11| ^ σ * z.re : ℝ) : ℂ) + ((|D.A22| ^ σ * z.im : ℝ) : ℂ) * I)

/-- Hypotheses: an inner family as in `FamData.Hyp`, and the inequalities between the abstract
constants used by the five-segment construction. -/
structure Hyp : Prop where
  pdag_pos : 0 < D.pdag
  A11_neg : D.A11 < 0
  A22_neg : D.A22 < 0
  A11_mul_A22 : D.A11 * D.A22 = 1
  smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => D.q p.1 p.2) (Icc 0 1 ×ˢ D.srcDisk)
  q_zero : ∀ z, D.q 0 z = D.b + D.A0 z
  injOn : ∀ σ ∈ Icc (0 : ℝ) 1, InjOn (D.q σ) D.srcDisk
  diff : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ z ∈ D.srcDisk, DifferentiableAt ℝ (D.q σ) z
  det : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ z ∈ D.srcDisk,
    LinearMap.det (fderiv ℝ (D.q σ) z : ℂ →ₗ[ℝ] ℂ) = 1
  bound : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ z ∈ D.srcDisk, ‖D.q σ z - D.b‖ ≤ D.Bstar
  bound_one : ∀ z ∈ D.srcDisk, ‖D.q 1 z‖ ≤ D.Rq
  c_pos : 0 < D.c
  c_le_one : D.c ≤ 1
  B3_ge : D.Rdag * max 1 (max |D.A11| |D.A22|) ≤ D.B3
  Rdag_le : D.Rdag ≤ D.Rsupp
  rbB3_le : D.rb + D.c * D.B3 ≤ D.Rsupp
  rbBstar_le : D.rb + D.c * D.Bstar ≤ D.Rsupp
  Rq_le : D.Rq ≤ D.Rsupp
  Psupp_lt_h : π * D.Rsupp ^ 2 < D.h

variable {D}

section hyp
variable (hD : D.Hyp)
include hD

lemma Rdag_pos : 0 < D.Rdag := Real.sqrt_pos.2 (div_pos hD.pdag_pos Real.pi_pos)

lemma rb_nonneg : 0 ≤ D.rb := norm_nonneg _

lemma norm_lt_Rdag {z : ℂ} (hz : z ∈ D.srcDisk) : ‖z‖ < D.Rdag := by
  have hpi := Real.pi_pos
  rw [Rdag, ← Real.sqrt_sq (norm_nonneg z)]
  exact Real.sqrt_lt_sqrt (sq_nonneg _)
    (by rw [lt_div_iff₀ hpi]; have : π * ‖z‖ ^ 2 < D.pdag := hz; linarith)

theorem cnew_pos : 0 < D.cnew ∧ D.cnew ≤ 1 := ⟨hD.c_pos, hD.c_le_one⟩

theorem Psupp_lt : D.Psupp < D.h := hD.Psupp_lt_h

lemma abs_A11_pos : 0 < |D.A11| := abs_pos.mpr hD.A11_neg.ne
lemma abs_A22_pos : 0 < |D.A22| := abs_pos.mpr hD.A22_neg.ne

lemma abs_A11_mul_A22 : |D.A11| * |D.A22| = 1 := by rw [← abs_mul, hD.A11_mul_A22, abs_one]

end hyp

lemma Msig_re_im (σ : ℝ) (z : ℂ) :
    D.Msig σ z = Complex.exp (((π * σ : ℝ) : ℂ) * I) *
      (((|D.A11| ^ σ * z.re : ℝ) : ℂ) + ((|D.A22| ^ σ * z.im : ℝ) : ℂ) * I) := rfl

variable (D) in
/-- `𝐌_σ` as a continuous linear map. -/
def MsigL (σ : ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.exp (((π * σ : ℝ) : ℂ) * I) •
    (ofRealCLM.comp ((|D.A11| ^ σ) • reCLM) + (ofRealCLM.comp ((|D.A22| ^ σ) • imCLM)).smulRight I)

lemma MsigL_apply (σ : ℝ) (z : ℂ) : D.MsigL σ z = D.Msig σ z := by
  simp [MsigL, Msig_re_im]; ring

lemma Msig_eq : D.Msig = fun σ => ⇑(D.MsigL σ) := funext fun σ => funext fun z =>
  (MsigL_apply σ z).symm

theorem Msig_det (hD : D.Hyp) (σ : ℝ) : LinearMap.det (D.MsigL σ : ℂ →ₗ[ℝ] ℂ) = 1 := by
  rw [Inner.det_eq_re_im]
  simp only [ContinuousLinearMap.coe_coe, MsigL_apply, Msig_re_im]
  set c := Real.cos (π * σ)
  set sn := Real.sin (π * σ)
  have he : Complex.exp (((π * σ : ℝ) : ℂ) * I) = (c : ℂ) + (sn : ℂ) * I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [he]
  simp
  have h1 : (|D.A11| ^ σ) * (|D.A22| ^ σ) = 1 := by
    rw [← Real.mul_rpow (abs_nonneg _) (abs_nonneg _), abs_A11_mul_A22 hD, Real.one_rpow]
  have h2 := Real.cos_sq_add_sin_sq (π * σ)
  linear_combination (c ^ 2 + sn ^ 2) * h1 + h2

lemma Msig_zero (z : ℂ) : D.Msig 0 z = z := by
  rw [Msig_re_im]; simp

lemma Msig_one (hD : D.Hyp) (z : ℂ) : D.Msig 1 z = D.A0 z := by
  rw [Msig_re_im, A0_apply, abs_of_neg hD.A11_neg, abs_of_neg hD.A22_neg]
  simp only [Real.rpow_one, mul_one]
  rw [show ((π : ℝ) : ℂ) * I = (π : ℂ) * I from rfl, Complex.exp_pi_mul_I]
  push_cast; ring

lemma rpow_le_max {d σ : ℝ} (hd : 0 < d) (hσ : σ ∈ Icc (0 : ℝ) 1) : d ^ σ ≤ max 1 d := by
  rcases le_or_gt 1 d with h | h
  · exact (by simpa using Real.rpow_le_rpow_of_exponent_le h hσ.2 : d ^ σ ≤ d).trans
      (le_max_right _ _)
  · exact (Real.rpow_le_one hd.le h.le hσ.1).trans (le_max_left _ _)

theorem Msig_norm_le (hD : D.Hyp) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : ‖z‖ ≤ D.Rdag) : ‖D.Msig σ z‖ ≤ D.B3 := by
  set M := max 1 (max |D.A11| |D.A22|)
  have hD0 : 0 ≤ M := zero_le_one.trans (le_max_left _ _)
  have hd1 : |D.A11| ^ σ ≤ M := (rpow_le_max (abs_A11_pos hD) hσ).trans
    (max_le_max le_rfl (le_max_left _ _))
  have hd2 : |D.A22| ^ σ ≤ M := (rpow_le_max (abs_A22_pos hD) hσ).trans
    (max_le_max le_rfl (le_max_right _ _))
  have hd1' : 0 ≤ |D.A11| ^ σ := Real.rpow_nonneg (abs_nonneg _) _
  have hd2' : 0 ≤ |D.A22| ^ σ := Real.rpow_nonneg (abs_nonneg _) _
  rw [Msig, Inner.norm_Rot]
  set a := |D.A11| ^ σ * z.re
  set b := |D.A22| ^ σ * z.im
  have hn : ‖((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * I‖ = √(a ^ 2 + b ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp; ring_nf
  rw [hn]
  have hz2 : z.re ^ 2 + z.im ^ 2 ≤ D.Rdag ^ 2 := by
    have : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    rw [← this]; exact pow_le_pow_left₀ (norm_nonneg z) hz 2
  have ha : a ^ 2 ≤ M ^ 2 * z.re ^ 2 := by
    simp only [a]; rw [mul_pow]; gcongr
  have hb : b ^ 2 ≤ M ^ 2 * z.im ^ 2 := by
    simp only [b]; rw [mul_pow]; gcongr
  calc √(a ^ 2 + b ^ 2) ≤ √((D.Rdag * M) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
    _ = D.Rdag * M := by rw [Real.sqrt_sq (mul_nonneg (Rdag_pos hD).le hD0)]
    _ ≤ D.B3 := hD.B3_ge

lemma Rdag_le_B3 (hD : D.Hyp) : D.Rdag ≤ D.B3 := by
  have := Rdag_pos hD
  have h1 := le_max_left 1 (max |D.A11| |D.A22|)
  have := hD.B3_ge
  nlinarith

lemma Msig_contDiff (hD : D.Hyp) : ContDiff ℝ ∞ (fun p : ℝ × ℂ => D.Msig p.1 p.2) := by
  have hr1 : ContDiff ℝ ∞ (fun σ : ℝ => |D.A11| ^ σ) :=
    contDiff_const.rpow contDiff_id fun _ => (abs_A11_pos hD).ne'
  have hr2 : ContDiff ℝ ∞ (fun σ : ℝ => |D.A22| ^ σ) :=
    contDiff_const.rpow contDiff_id fun _ => (abs_A22_pos hD).ne'
  have hre : ContDiff ℝ ∞ (fun p : ℝ × ℂ => p.2.re) := reCLM.contDiff.comp contDiff_snd
  have him : ContDiff ℝ ∞ (fun p : ℝ × ℂ => p.2.im) := imCLM.contDiff.comp contDiff_snd
  simp only [Msig_re_im]
  exact ((Complex.contDiff_exp (𝕜 := ℝ)).comp ((ofRealCLM.contDiff.comp
    (contDiff_const.mul contDiff_fst)).mul contDiff_const)).mul
    ((ofRealCLM.contDiff.comp ((hr1.comp contDiff_fst).mul hre)).add
      ((ofRealCLM.contDiff.comp ((hr2.comp contDiff_fst).mul him)).mul contDiff_const))

/-! ### The five segments and the path -/

/-- The flat clock `σ_j(t) = S(5t - j)`. -/
def clock (j : ℕ) (t : ℝ) : ℝ := Real.smoothTransition (5 * t - j)

variable (D) in
/-- The five segments. -/
def seg : ℕ → ℝ → ℂ → ℂ
  | 0, σ, z => ((D.cnew ^ σ : ℝ) : ℂ) * z
  | 1, σ, z => (σ : ℂ) * D.b + (D.cnew : ℂ) * z
  | 2, σ, z => D.b + (D.cnew : ℂ) * D.Msig σ z
  | 3, σ, z => D.b + (D.cnew : ℂ) * (D.q σ z - D.b)
  | _, σ, z => D.b + ((D.cnew ^ (1 - σ) : ℝ) : ℂ) * (D.q 1 z - D.b)

variable (D) in
/-- The ordinary path, one telescoped formula in the clocks. -/
def ordPath (t : ℝ) (z : ℂ) : ℂ :=
  ((D.cnew ^ clock 0 t : ℝ) : ℂ) * z + (clock 1 t : ℂ) * D.b +
    (D.cnew : ℂ) * (D.Msig (clock 2 t) z - z) +
    (D.cnew : ℂ) * (D.q (clock 3 t) z - D.b - D.A0 z) +
    ((D.cnew ^ (1 - clock 4 t) - D.cnew : ℝ) : ℂ) * (D.q 1 z - D.b)

variable (D) in
/-- `γ_t = c^{2S(5t) - 2S(5t-4)}`. -/
def gammaDet (t : ℝ) : ℝ := D.cnew ^ (2 * clock 0 t - 2 * clock 4 t)

lemma clock_mem (j : ℕ) (t : ℝ) : clock j t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

lemma clock_eq_zero {j : ℕ} {t : ℝ} (h : 5 * t ≤ j) : clock j t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma clock_eq_one {j : ℕ} {t : ℝ} (h : (j : ℝ) + 1 ≤ 5 * t) : clock j t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma clock_contDiff (j : ℕ) : ContDiff ℝ ∞ (clock j) :=
  Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)

lemma clock4_le_clock0 (t : ℝ) : clock 4 t ≤ clock 0 t :=
  Real.smoothTransition.monotone (by push_cast; linarith)

section hyp2
variable (hD : D.Hyp)
include hD

lemma ordPath_of_nonpos {t : ℝ} (ht : t ≤ 0) (z : ℂ) : D.ordPath t z = z := by
  have h : ∀ j : ℕ, clock j t = 0 := fun j => clock_eq_zero (by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
  simp only [ordPath, h, Real.rpow_zero, Msig_zero, hD.q_zero, sub_zero]
  simp

lemma ordPath_of_one_le {t : ℝ} (ht : 1 ≤ t) (z : ℂ) : D.ordPath t z = D.q 1 z := by
  have h : ∀ j : ℕ, j ≤ 4 → clock j t = 1 := fun j hj => clock_eq_one (by
    have : (j : ℝ) ≤ 4 := by exact_mod_cast hj
    linarith)
  simp only [ordPath, h 0 (by norm_num), h 1 (by norm_num), h 2 (by norm_num), h 3 (by norm_num),
    h 4 le_rfl, Real.rpow_one, Msig_one hD, sub_self, Real.rpow_zero]
  push_cast; ring

theorem ordPath_eq_seg {j : ℕ} (hj : j ≤ 4) {t : ℝ} (ht : t ∈ Icc ((j : ℝ) / 5) ((j + 1) / 5))
    (z : ℂ) : D.ordPath t z = D.seg j (clock j t) z := by
  have h5 : (j : ℝ) ≤ 5 * t ∧ 5 * t ≤ j + 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hlo : ∀ i : ℕ, i < j → clock i t = 1 := fun i hi => clock_eq_one (by
    have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hi
    linarith)
  have hhi : ∀ i : ℕ, j < i → clock i t = 0 := fun i hi => clock_eq_zero (by
    have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hi
    linarith)
  interval_cases j
  · simp only [ordPath, seg, hhi 1 (by norm_num), hhi 2 (by norm_num), hhi 3 (by norm_num),
      hhi 4 (by norm_num), Msig_zero, hD.q_zero, sub_zero, Real.rpow_one]
    push_cast; ring
  · simp only [ordPath, seg, hlo 0 (by norm_num), hhi 2 (by norm_num), hhi 3 (by norm_num),
      hhi 4 (by norm_num), Msig_zero, hD.q_zero, sub_zero, Real.rpow_one]
    push_cast; ring
  · simp only [ordPath, seg, hlo 0 (by norm_num), hlo 1 (by norm_num), hhi 3 (by norm_num),
      hhi 4 (by norm_num), hD.q_zero, sub_zero, Real.rpow_one]
    push_cast; ring
  · simp only [ordPath, seg, hlo 0 (by norm_num), hlo 1 (by norm_num), hlo 2 (by norm_num),
      hhi 4 (by norm_num), Msig_one hD, Real.rpow_one, sub_zero]
    push_cast; ring
  · simp only [ordPath, seg, hlo 0 (by norm_num), hlo 1 (by norm_num), hlo 2 (by norm_num),
      hlo 3 (by norm_num), Msig_one hD, Real.rpow_one]
    push_cast; ring

end hyp2

theorem time_cases {Q : ℝ → Prop} (h0 : ∀ t ≤ 0, Q t) (h1 : ∀ t, 1 ≤ t → Q t)
    (hj : ∀ j : ℕ, j ≤ 4 → ∀ t ∈ Icc ((j : ℝ) / 5) ((j + 1) / 5), Q t) (t : ℝ) : Q t := by
  rcases le_or_gt t 0 with ht | ht
  · exact h0 t ht
  rcases le_or_gt t (1 / 5) with ht1 | ht1
  · exact hj 0 (by norm_num) t ⟨by norm_num; linarith, by norm_num; linarith⟩
  rcases le_or_gt t (2 / 5) with ht2 | ht2
  · exact hj 1 (by norm_num) t ⟨by norm_num; linarith, by norm_num; linarith⟩
  rcases le_or_gt t (3 / 5) with ht3 | ht3
  · exact hj 2 (by norm_num) t ⟨by norm_num; linarith, by norm_num; linarith⟩
  rcases le_or_gt t (4 / 5) with ht4 | ht4
  · exact hj 3 (by norm_num) t ⟨by norm_num; linarith, by norm_num; linarith⟩
  rcases le_or_gt t 1 with ht5 | ht5
  · exact hj 4 le_rfl t ⟨by norm_num; linarith, by norm_num; linarith⟩
  · exact h1 t ht5.le

section hyp3
variable (hD : D.Hyp)
include hD

lemma cpow_contDiff (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun t => D.cnew ^ f t) :=
  contDiff_const.rpow hf fun _ => (cnew_pos hD).1.ne'

theorem ordPath_smooth :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => D.ordPath p.1 p.2) (univ ×ˢ D.srcDisk) := by
  have hq := hD.smooth
  have hc : ∀ j, ContDiff ℝ ∞ (fun p : ℝ × ℂ => clock j p.1) := fun j =>
    (clock_contDiff j).comp contDiff_fst
  have hq3 : ContDiffOn ℝ ∞ ((fun q : ℝ × ℂ => D.q q.1 q.2) ∘
      (fun p : ℝ × ℂ => (clock 3 p.1, p.2))) (univ ×ˢ D.srcDisk) :=
    hq.comp ((hc 3).contDiffOn.prodMk contDiffOn_snd) fun p hp => ⟨clock_mem 3 p.1, hp.2⟩
  have hq1 : ContDiffOn ℝ ∞ ((fun q : ℝ × ℂ => D.q q.1 q.2) ∘
      (fun p : ℝ × ℂ => ((1 : ℝ), p.2))) (univ ×ˢ D.srcDisk) :=
    hq.comp ((contDiffOn_const (c := (1 : ℝ))).prodMk contDiffOn_snd)
      fun p hp => ⟨⟨zero_le_one, le_rfl⟩, hp.2⟩
  have hM : ContDiff ℝ ∞ (fun p : ℝ × ℂ => D.Msig (clock 2 p.1) p.2) :=
    (Msig_contDiff hD).comp ((hc 2).prodMk contDiff_snd)
  have hA : ContDiff ℝ ∞ (fun p : ℝ × ℂ => D.A0 p.2) := D.A0.contDiff.comp contDiff_snd
  have hz : ContDiff ℝ ∞ (fun p : ℝ × ℂ => p.2) := contDiff_snd
  have hc0 : ContDiff ℝ ∞ (fun p : ℝ × ℂ => ((D.cnew ^ clock 0 p.1 : ℝ) : ℂ)) :=
    ofRealCLM.contDiff.comp ((cpow_contDiff hD _ (clock_contDiff 0)).comp contDiff_fst)
  have hc4 : ContDiff ℝ ∞
      (fun p : ℝ × ℂ => ((D.cnew ^ (1 - clock 4 p.1) - D.cnew : ℝ) : ℂ)) :=
    ofRealCLM.contDiff.comp (((cpow_contDiff hD _ (contDiff_const.sub (clock_contDiff 4))).sub
      contDiff_const).comp contDiff_fst)
  have hc1 : ContDiff ℝ ∞ (fun p : ℝ × ℂ => (clock 1 p.1 : ℂ)) :=
    ofRealCLM.contDiff.comp (hc 1)
  set S := univ ×ˢ D.srcDisk
  have t1 : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => ((D.cnew ^ clock 0 p.1 : ℝ) : ℂ) * p.2) S :=
    (hc0.mul hz).contDiffOn
  have t2 : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => (clock 1 p.1 : ℂ) * D.b) S :=
    (hc1.mul contDiff_const).contDiffOn
  have t3 : ContDiffOn ℝ ∞
      (fun p : ℝ × ℂ => (D.cnew : ℂ) * (D.Msig (clock 2 p.1) p.2 - p.2)) S :=
    (contDiff_const.mul (hM.sub hz)).contDiffOn
  have t4 := (contDiffOn_const (c := (D.cnew : ℂ))).mul
    ((hq3.sub (contDiffOn_const (c := D.b))).sub hA.contDiffOn)
  have t5 := hc4.contDiffOn.mul (hq1.sub (contDiffOn_const (c := D.b)))
  refine ((((t1.add t2).add t3).add t4).add t5).congr fun p _ => ?_
  simp only [ordPath, Function.comp]

lemma ofReal_ne_zero_of_pos {r : ℝ} (hr : 0 < r) : (r : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr hr.ne'

theorem seg_injOn {j : ℕ} {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) : InjOn (D.seg j σ) D.srcDisk := by
  have hc := (cnew_pos hD).1
  have hc' := ofReal_ne_zero_of_pos hD hc
  intro z₁ hz₁ z₂ hz₂ h
  match j with
  | 0 =>
    simp only [seg] at h
    exact mul_left_cancel₀ (ofReal_ne_zero_of_pos hD (Real.rpow_pos_of_pos hc σ)) h
  | 1 =>
    simp only [seg, add_right_inj] at h
    exact mul_left_cancel₀ hc' h
  | 2 =>
    simp only [seg, add_right_inj] at h
    have h' := mul_left_cancel₀ hc' h
    rw [Msig_eq] at h'
    exact Inner.injective_of_det_ne_zero _ (by rw [Msig_det hD]; norm_num) h'
  | 3 =>
    simp only [seg, add_right_inj] at h
    exact hD.injOn σ hσ hz₁ hz₂ (sub_left_inj.mp (mul_left_cancel₀ hc' h))
  | j + 4 =>
    simp only [seg, add_right_inj] at h
    exact hD.injOn 1 ⟨zero_le_one, le_rfl⟩ hz₁ hz₂
      (sub_left_inj.mp (mul_left_cancel₀
        (ofReal_ne_zero_of_pos hD (Real.rpow_pos_of_pos hc _)) h))

theorem ordPath_injOn (t : ℝ) : InjOn (D.ordPath t) D.srcDisk := by
  refine time_cases (Q := fun t => InjOn (D.ordPath t) D.srcDisk) ?_ ?_ ?_ t
  · intro t ht
    have : D.ordPath t = id := funext (ordPath_of_nonpos hD ht)
    rw [this]; exact injOn_id _
  · intro t ht
    have : D.ordPath t = D.q 1 := funext (ordPath_of_one_le hD ht)
    rw [this]; exact hD.injOn 1 ⟨zero_le_one, le_rfl⟩
  · intro j hj t ht
    have : D.ordPath t = D.seg j (clock j t) := funext (ordPath_eq_seg hD hj ht)
    rw [this]; exact seg_injOn hD (clock_mem j t)

end hyp3

lemma det_affine_scale {F : ℂ → ℂ} {z : ℂ} (hF : DifferentiableAt ℝ F z) (p : ℂ) (r : ℝ) :
    LinearMap.det (fderiv ℝ (fun z => p + (r : ℂ) * F z) z : ℂ →ₗ[ℝ] ℂ) =
      r ^ 2 * LinearMap.det (fderiv ℝ F z : ℂ →ₗ[ℝ] ℂ) := by
  have h := (hF.hasFDerivAt.const_mul (r : ℂ)).const_add p
  have hsm : ((r : ℂ) • fderiv ℝ F z : ℂ →L[ℝ] ℂ) = r • fderiv ℝ F z := by
    ext1 x; simp [Complex.real_smul]
  rw [h.fderiv, hsm, ContinuousLinearMap.toLinearMap_smul, LinearMap.det_smul,
    Complex.finrank_real_complex]

section hyp4
variable (hD : D.Hyp)
include hD

lemma cnew_rpow_sq (x : ℝ) : (D.cnew ^ x) ^ 2 = D.cnew ^ (2 * x) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (cnew_pos hD).1.le]; norm_num; ring_nf

theorem seg_det {j : ℕ} (hj : j ≤ 4) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : z ∈ D.srcDisk) :
    LinearMap.det (fderiv ℝ (D.seg j σ) z : ℂ →ₗ[ℝ] ℂ) =
      if j = 0 then D.cnew ^ (2 * σ) else if j = 4 then D.cnew ^ (2 - 2 * σ)
        else D.cnew ^ 2 := by
  have hid : DifferentiableAt ℝ (fun z : ℂ => z) z := differentiableAt_id
  have hq1 := hD.diff 1 ⟨zero_le_one, le_rfl⟩ z hz
  have hqs := hD.diff σ hσ z hz
  interval_cases j
  · have hfun : D.seg 0 σ = fun z => 0 + ((D.cnew ^ σ : ℝ) : ℂ) * z := by
      funext z; simp [seg]
    rw [hfun, det_affine_scale hid, fderiv_fun_id, ContinuousLinearMap.coe_id, LinearMap.det_id,
      mul_one, cnew_rpow_sq hD]
    simp
  · have hfun : D.seg 1 σ = fun z => (σ : ℂ) * D.b + ((D.cnew : ℝ) : ℂ) * z := rfl
    rw [hfun, det_affine_scale hid, fderiv_fun_id, ContinuousLinearMap.coe_id, LinearMap.det_id]
    simp
  · have hfun : D.seg 2 σ = fun z => D.b + ((D.cnew : ℝ) : ℂ) * D.MsigL σ z := by
      funext z; simp [seg, MsigL_apply]
    rw [hfun, det_affine_scale (D.MsigL σ).differentiableAt, ContinuousLinearMap.fderiv,
      Msig_det hD]
    simp
  · have hfun : D.seg 3 σ = fun z => D.b + ((D.cnew : ℝ) : ℂ) * (D.q σ z - D.b) := rfl
    rw [hfun, det_affine_scale (hqs.sub_const _)]
    have : fderiv ℝ (fun z => D.q σ z - D.b) z = fderiv ℝ (D.q σ) z :=
      fderiv_sub_const _
    rw [this, hD.det σ hσ z hz]
    simp
  · have hfun : D.seg 4 σ = fun z => D.b + ((D.cnew ^ (1 - σ) : ℝ) : ℂ) *
        (D.q 1 z - D.b) := rfl
    rw [hfun, det_affine_scale (hq1.sub_const _)]
    have : fderiv ℝ (fun z => D.q 1 z - D.b) z = fderiv ℝ (D.q 1) z :=
      fderiv_sub_const _
    rw [this, hD.det 1 ⟨zero_le_one, le_rfl⟩ z hz, cnew_rpow_sq hD]
    simp; ring_nf

theorem ordPath_det (t : ℝ) {z : ℂ} (hz : z ∈ D.srcDisk) :
    LinearMap.det (fderiv ℝ (D.ordPath t) z : ℂ →ₗ[ℝ] ℂ) = D.gammaDet t := by
  refine time_cases (Q := fun t => LinearMap.det (fderiv ℝ (D.ordPath t) z : ℂ →ₗ[ℝ] ℂ) =
    D.gammaDet t) ?_ ?_ ?_ t
  · intro t ht
    have : D.ordPath t = id := funext (ordPath_of_nonpos hD ht)
    have h0 : ∀ j : ℕ, clock j t = 0 := fun j => clock_eq_zero (by
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    rw [this, fderiv_id, ContinuousLinearMap.coe_id, LinearMap.det_id, gammaDet, h0, h0]
    simp
  · intro t ht
    have : D.ordPath t = D.q 1 := funext (ordPath_of_one_le hD ht)
    have h1 : ∀ j : ℕ, j ≤ 4 → clock j t = 1 := fun j hj => clock_eq_one (by
      have : (j : ℝ) ≤ 4 := by exact_mod_cast hj
      linarith)
    rw [this, hD.det 1 ⟨zero_le_one, le_rfl⟩ z hz, gammaDet,
      h1 0 (by norm_num), h1 4 le_rfl]
    simp
  · intro j hj t ht
    have hfun : D.ordPath t = D.seg j (clock j t) := funext (ordPath_eq_seg hD hj ht)
    have h5a : (j : ℝ) ≤ 5 * t := by linarith [ht.1]
    have h5b : 5 * t ≤ j + 1 := by linarith [ht.2]
    rw [hfun, seg_det hD hj (clock_mem j t) hz, gammaDet]
    interval_cases j
    · norm_num at h5a h5b
      have h4 : clock 4 t = 0 := clock_eq_zero (by norm_num; linarith)
      simp [h4]
    · norm_num at h5a h5b
      have h0 : clock 0 t = 1 := clock_eq_one (by norm_num; linarith)
      have h4 : clock 4 t = 0 := clock_eq_zero (by norm_num; linarith)
      simp [h0, h4]
    · norm_num at h5a h5b
      have h0 : clock 0 t = 1 := clock_eq_one (by norm_num; linarith)
      have h4 : clock 4 t = 0 := clock_eq_zero (by norm_num; linarith)
      simp [h0, h4]
    · norm_num at h5a h5b
      have h0 : clock 0 t = 1 := clock_eq_one (by norm_num; linarith)
      have h4 : clock 4 t = 0 := clock_eq_zero (by norm_num; linarith)
      simp [h0, h4]
    · norm_num at h5a h5b
      have h0 : clock 0 t = 1 := clock_eq_one (by norm_num; linarith)
      simp [h0]

theorem gammaDet_bounds (t : ℝ) :
    D.cnew ^ 2 ≤ D.gammaDet t ∧ D.gammaDet t ≤ 1 ∧ D.gammaDet 0 = 1 ∧ D.gammaDet 1 = 1 := by
  have hc := cnew_pos hD
  have hc1 : D.cnew ≤ 1 := by linarith [hc.2]
  have h40 := clock4_le_clock0 t
  have h0 := clock_mem 0 t
  have h4 := clock_mem 4 t
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := Real.rpow_le_rpow_of_exponent_ge hc.1 hc1
      (show 2 * clock 0 t - 2 * clock 4 t ≤ 2 by linarith [h0.2, h4.1])
    rw [gammaDet]; simpa using this
  · exact Real.rpow_le_one hc.1.le hc1 (by linarith)
  · rw [gammaDet, clock_eq_zero (j := 0) (by norm_num), clock_eq_zero (j := 4) (by norm_num)]
    simp
  · rw [gammaDet, clock_eq_one (j := 0) (by norm_num), clock_eq_one (j := 4) (by norm_num)]
    simp

lemma rb_le_Rsupp : D.rb ≤ D.Rsupp := by
  have := mul_nonneg (cnew_pos hD).1.le ((Rdag_pos hD).le.trans (Rdag_le_B3 hD))
  have := hD.rbB3_le
  exact (by unfold cnew at *; linarith : D.rb ≤ D.Rsupp)

theorem seg_image {j : ℕ} {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) 1) {z : ℂ} (hz : z ∈ D.srcDisk) :
    ‖D.seg j σ z‖ ≤ D.Rsupp := by
  have hc := cnew_pos hD
  have hzR := (norm_lt_Rdag hD hz).le
  have hb : ‖D.b‖ = D.rb := rfl
  have hrb := rb_nonneg hD
  have hR1 : D.Rdag ≤ D.Rsupp := hD.Rdag_le
  have hR2 : D.rb + D.cnew * D.B3 ≤ D.Rsupp := hD.rbB3_le
  have hR3 : D.rb + D.cnew * D.Bstar ≤ D.Rsupp := hD.rbBstar_le
  have hR4 : D.Rq ≤ D.Rsupp := hD.Rq_le
  have hcB : D.cnew * D.Rdag ≤ D.cnew * D.B3 :=
    mul_le_mul_of_nonneg_left (Rdag_le_B3 hD) hc.1.le
  match j with
  | 0 =>
    simp only [seg]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hc.1.le _)]
    have := Real.rpow_le_one hc.1.le (by linarith [hc.2]) hσ.1
    nlinarith [norm_nonneg z]
  | 1 =>
    simp only [seg]
    calc ‖(σ : ℂ) * D.b + (D.cnew : ℂ) * z‖ ≤ ‖(σ : ℂ) * D.b‖ + ‖(D.cnew : ℂ) * z‖ :=
          norm_add_le _ _
      _ = σ * D.rb + D.cnew * ‖z‖ := by
          rw [norm_mul, norm_mul, hb, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg hσ.1, Real.norm_of_nonneg hc.1.le]
      _ ≤ 1 * D.rb + D.cnew * D.Rdag := by
          have := mul_le_mul_of_nonneg_left hzR hc.1.le
          have := mul_le_mul_of_nonneg_right hσ.2 hrb
          linarith
      _ ≤ D.Rsupp := by linarith
  | 2 =>
    simp only [seg]
    calc ‖D.b + (D.cnew : ℂ) * D.Msig σ z‖ ≤ ‖D.b‖ + ‖(D.cnew : ℂ) * D.Msig σ z‖ :=
          norm_add_le _ _
      _ = D.rb + D.cnew * ‖D.Msig σ z‖ := by
          rw [norm_mul, hb, Complex.norm_real, Real.norm_of_nonneg hc.1.le]
      _ ≤ D.rb + D.cnew * D.B3 := by
          have := mul_le_mul_of_nonneg_left (Msig_norm_le hD hσ hzR) hc.1.le; linarith
      _ ≤ D.Rsupp := hR2
  | 3 =>
    simp only [seg]
    calc ‖D.b + (D.cnew : ℂ) * (D.q σ z - D.b)‖
        ≤ ‖D.b‖ + ‖(D.cnew : ℂ) * (D.q σ z - D.b)‖ := norm_add_le _ _
      _ = D.rb + D.cnew * ‖D.q σ z - D.b‖ := by
          rw [norm_mul, hb, Complex.norm_real, Real.norm_of_nonneg hc.1.le]
      _ ≤ D.rb + D.cnew * D.Bstar := by
          have := mul_le_mul_of_nonneg_left (hD.bound σ hσ z hz) hc.1.le
          linarith
      _ ≤ D.Rsupp := hR3
  | j + 4 =>
    simp only [seg]
    set μ := D.cnew ^ (1 - σ)
    have hμ0 : 0 ≤ μ := Real.rpow_nonneg hc.1.le _
    have hμ1 : μ ≤ 1 := Real.rpow_le_one hc.1.le (by linarith [hc.2]) (by linarith [hσ.2])
    have hq := hD.bound_one z hz
    have heq : D.b + (μ : ℂ) * (D.q 1 z - D.b) =
        ((1 - μ : ℝ) : ℂ) * D.b + (μ : ℂ) * D.q 1 z := by push_cast; ring
    rw [heq]
    calc ‖((1 - μ : ℝ) : ℂ) * D.b + (μ : ℂ) * D.q 1 z‖
        ≤ ‖((1 - μ : ℝ) : ℂ) * D.b‖ + ‖(μ : ℂ) * D.q 1 z‖ := norm_add_le _ _
      _ = (1 - μ) * D.rb + μ * ‖D.q 1 z‖ := by
          rw [norm_mul, norm_mul, hb, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg hμ0]
      _ ≤ (1 - μ) * D.Rsupp + μ * D.Rsupp := by
          have h1 := mul_le_mul_of_nonneg_left (rb_le_Rsupp hD) (by linarith : (0 : ℝ) ≤ 1 - μ)
          have h2 := mul_le_mul_of_nonneg_left (hq.trans hR4) hμ0
          linarith
      _ = D.Rsupp := by ring

theorem ordPath_image (t : ℝ) {z : ℂ} (hz : z ∈ D.srcDisk) : ‖D.ordPath t z‖ ≤ D.Rsupp := by
  refine time_cases (Q := fun t => ‖D.ordPath t z‖ ≤ D.Rsupp) ?_ ?_ ?_ t
  · intro t ht
    rw [ordPath_of_nonpos hD ht]
    exact (norm_lt_Rdag hD hz).le.trans hD.Rdag_le
  · intro t ht
    rw [ordPath_of_one_le hD ht]
    exact (hD.bound_one z hz).trans hD.Rq_le
  · intro j hj t ht
    rw [ordPath_eq_seg hD hj ht]
    exact seg_image hD (clock_mem j t) hz

theorem ordPath_image_area (t : ℝ) {z : ℂ} (hz : z ∈ D.srcDisk) :
    π * ‖D.ordPath t z‖ ^ 2 ≤ D.Psupp := by
  have h := ordPath_image hD t hz
  unfold Psupp
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) h 2) Real.pi_pos.le

theorem gammaDet_contDiff : ContDiff ℝ ∞ D.gammaDet :=
  cpow_contDiff hD _ ((contDiff_const.mul (clock_contDiff 0)).sub
    (contDiff_const.mul (clock_contDiff 4)))

end hyp4

variable (D) in
/-- The path data of the five-segment path, with source-order parameter `e`. -/
def pathData (e : ℝ) : Qhat.PathData where
  path := D.ordPath
  gam := D.gammaDet
  h := D.h
  e := e
  pdag := D.pdag
  Psupp := D.Psupp
  c := D.cnew

/-- **The five-segment path is ordinary.** -/
theorem ordinary (hD : D.Hyp) {e : ℝ} (he : 0 < e) (h4e : 4 * e < D.h)
    (hpd : D.h - 15 * e / 4 < D.pdag) : Qhat.OrdinaryPath (D.pathData e) where
  e_pos := he
  four_e_lt_h := h4e
  pplus_lt_pdag := hpd
  Psupp_lt_h := Psupp_lt hD
  c_pos := (cnew_pos hD).1
  smooth := ordPath_smooth hD
  eq_id := fun _ ht z _ => ordPath_of_nonpos hD ht z
  eq_one := fun t ht z _ => by
    show D.ordPath t z = D.ordPath 1 z
    rw [ordPath_of_one_le hD ht, ordPath_of_one_le hD le_rfl]
  injOn := ordPath_injOn hD
  det := fun t _ hz => ordPath_det hD t hz
  gam_smooth := gammaDet_contDiff hD
  gam_ge := fun t => (gammaDet_bounds hD t).1
  gam_one := (gammaDet_bounds hD 0).2.2.2
  image := fun t _ hz => ordPath_image_area hD t hz

end FiveData

/-! ## Part 2: the instance for `PlanarGen.Input` -/

namespace Input

variable {m : ℕ} (D : Input m)

/-- The five-segment data of `D.pathData y`: inner family `q_{y,σ} = D.qin y σ`, centre
`b_y`, `𝐀₀(y)`, and the uniform constants of §6. -/
def fiveData (y : Moments m) : FiveData where
  q := D.qin y
  b := D.bpt y
  A11 := D.A11 y
  A22 := D.A22 y
  h := 1
  pdag := D.pdag
  c := D.cnew
  B3 := D.B3
  Bstar := D.Bstar
  Rq := D.Rq
  Rsupp := D.Rsupp

theorem fiveData_ordPath (y : Moments m) (t : ℝ) (z : ℂ) :
    (D.fiveData y).ordPath t z = D.ordPath y t z := by
  simp only [FiveData.ordPath, Input.ordPath, FiveData.A0_apply]
  rfl

theorem pathData_eq_five (y : Moments m) :
    D.pathData y = (D.fiveData y).pathData (2 * D.eta) := by
  have h1 : (D.fiveData y).ordPath = D.ordPath y :=
    funext fun t => funext fun z => D.fiveData_ordPath y t z
  simp only [Input.pathData, FiveData.pathData, h1]
  rfl

/-- The inner-family properties of `q_{y,σ} = D.qin y σ` on the source disc `D(p†)`
(`prop:pln-inner-family` uniformly in `y`). -/
structure InnerHyp (y : Moments m) : Prop where
  smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => D.qin y p.1 p.2)
    (Icc 0 1 ×ˢ {z : ℂ | π * ‖z‖ ^ 2 < D.pdag})
  q_zero : ∀ z, D.qin y 0 z = D.bpt y + D.A0 y z
  injOn : ∀ σ ∈ Icc (0 : ℝ) 1, InjOn (D.qin y σ) {z : ℂ | π * ‖z‖ ^ 2 < D.pdag}
  diff : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ z : ℂ, π * ‖z‖ ^ 2 < D.pdag →
    DifferentiableAt ℝ (D.qin y σ) z
  det : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ z : ℂ, π * ‖z‖ ^ 2 < D.pdag →
    LinearMap.det (fderiv ℝ (D.qin y σ) z : ℂ →ₗ[ℝ] ℂ) = 1
  bound : ∀ σ ∈ Icc (0 : ℝ) 1, ∀ z : ℂ, π * ‖z‖ ^ 2 < D.pdag → ‖D.qin y σ z - D.bpt y‖ ≤ D.Bstar
  bound_one : ∀ z : ℂ, π * ‖z‖ ^ 2 < D.pdag → ‖D.qin y 1 z‖ ≤ D.Rq

/-- Hypotheses at one parameter `y`: positivity of the data, the uniform Morse bounds
`r₀ ≤ v_*(y) ≤ 1 - r₀`, `α_min ≤ α_y ≤ α_max`, `b₀ > 0`, and the inner-family properties. -/
structure YHyp (y : Moments m) : Prop where
  xi_pos : 0 < D.xi
  L_nonneg : 0 ≤ D.L
  M_nonneg : 0 ≤ D.M
  b0_pos : 0 < D.b0
  vstar_ge : D.r0 ≤ D.vstar y
  vstar_le : D.vstar y ≤ 1 - D.r0
  alpha_ge : D.alphaMin ≤ D.alphaU y
  alpha_le : D.alphaU y ≤ D.alphaMax
  inner : D.InnerHyp y

section consts

variable {D} {y : Moments m} (hY : D.YHyp y)
include hY

lemma kappa_pos' : 0 < D.kappa := kappa_pos hY.xi_pos hY.L_nonneg
lemma r0_pos' : 0 < D.r0 := r0_pos hY.xi_pos hY.L_nonneg
lemma eta_pos' : 0 < D.eta := eta_pos hY.xi_pos hY.L_nonneg

lemma alphaMin_pos : 0 < D.alphaMin := by
  unfold alphaMin; linarith [kappa_pos' hY]

lemma alphaU_pos : 0 < D.alphaU y := (alphaMin_pos hY).trans_le hY.alpha_ge

lemma alphaMax_pos : 0 < D.alphaMax := (alphaU_pos hY).trans_le hY.alpha_le

lemma vstar_pos : 0 < D.vstar y := (r0_pos' hY).trans_le hY.vstar_ge

lemma a0_pos : 0 < D.a0 y := Real.sqrt_pos.2 (div_pos two_pos (alphaU_pos hY))

lemma rb_pos : 0 < D.rb y := Real.sqrt_pos.2 (div_pos (vstar_pos hY) Real.pi_pos)

lemma j0_pos : 0 < D.j0 y := mul_pos (a0_pos hY) hY.b0_pos

lemma cx_pos : 0 < D.cx y := div_pos (a0_pos hY) (Real.sqrt_pos.2 (j0_pos hY))

lemma cy_pos : 0 < D.cy y := div_pos hY.b0_pos (Real.sqrt_pos.2 (j0_pos hY))

lemma A11_neg : D.A11 y < 0 := by
  unfold A11
  have := div_pos (cx_pos hY) (mul_pos (mul_pos two_pos Real.pi_pos) (rb_pos hY))
  linarith

lemma A22_neg : D.A22 y < 0 := by
  unfold A22
  have := mul_pos (mul_pos (mul_pos two_pos Real.pi_pos) (rb_pos hY)) (cy_pos hY)
  linarith

lemma A11_mul_A22 : D.A11 y * D.A22 y = 1 := by
  unfold A11 A22 cx cy j0
  have ha := a0_pos hY
  have hb := hY.b0_pos
  have hr := rb_pos hY
  have hpi := Real.pi_pos
  have hs : √(D.a0 y * D.b0) ^ 2 = D.a0 y * D.b0 := Real.sq_sqrt (by positivity)
  have hs0 : 0 < √(D.a0 y * D.b0) := Real.sqrt_pos.2 (by positivity)
  field_simp
  nlinarith [hs]

lemma rb_le_rbmax : D.rb y ≤ D.rbmax :=
  Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hY.vstar_le Real.pi_pos.le)

omit hY in
/-- `π · √(x/π) = √(π x)`. -/
lemma pi_mul_sqrt_div {x : ℝ} (hx : 0 ≤ x) : π * √(x / π) = √(π * x) := by
  have hpi := Real.pi_pos
  rw [← Real.sqrt_sq hpi.le, ← Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpi.le]
  congr 1; field_simp

lemma amin_le_a0 : D.amin ≤ D.a0 y :=
  Real.sqrt_le_sqrt (div_le_div_of_nonneg_left two_pos.le (alphaU_pos hY) hY.alpha_le)

lemma a0_le_amax : D.a0 y ≤ D.amax :=
  Real.sqrt_le_sqrt (div_le_div_of_nonneg_left two_pos.le (alphaMin_pos hY) hY.alpha_ge)

lemma amin_pos : 0 < D.amin := Real.sqrt_pos.2 (div_pos two_pos (alphaMax_pos hY))

lemma abs_A11_le : |D.A11 y| ≤ √(D.amax / D.b0) / (2 * √(π * D.r0)) := by
  rw [abs_of_neg (A11_neg hY), A11, neg_neg]
  unfold cx j0
  have ha := a0_pos hY
  have hb := hY.b0_pos
  have hpi := Real.pi_pos
  have hr0 := r0_pos' hY
  -- `a₀/√(a₀b₀) = √(a₀/b₀)` and `2π r_b = 2√(π v_*)`
  have h1 : D.a0 y / √(D.a0 y * D.b0) = √(D.a0 y / D.b0) := by
    rw [eq_comm, Real.sqrt_div' _ hb.le, div_eq_div_iff (Real.sqrt_pos.2 hb).ne'
      (Real.sqrt_pos.2 (mul_pos ha hb)).ne', Real.sqrt_mul ha.le, ← mul_assoc,
      Real.mul_self_sqrt ha.le]
  have h2 : 2 * π * D.rb y = 2 * √(π * D.vstar y) := by
    rw [mul_assoc, rb, pi_mul_sqrt_div (vstar_pos hY).le]
  rw [h1, h2]
  apply div_le_div₀ (Real.sqrt_nonneg _)
    (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (a0_le_amax hY) hb.le))
    (by have := Real.sqrt_pos.2 (mul_pos hpi hr0); linarith)
    (by have := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hY.vstar_ge hpi.le); linarith)

lemma abs_A22_le : |D.A22 y| ≤ 2 * √π * √(D.b0 / D.amin) := by
  rw [abs_of_neg (A22_neg hY), A22, neg_neg]
  unfold cy j0
  have ha := a0_pos hY
  have hb := hY.b0_pos
  have hpi := Real.pi_pos
  have h1 : D.b0 / √(D.a0 y * D.b0) = √(D.b0 / D.a0 y) := by
    rw [eq_comm, Real.sqrt_div' _ ha.le, div_eq_div_iff (Real.sqrt_pos.2 ha).ne'
      (Real.sqrt_pos.2 (mul_pos ha hb)).ne', Real.sqrt_mul ha.le, mul_comm (√(D.a0 y)),
      ← mul_assoc, Real.mul_self_sqrt hb.le, mul_comm]
  have h2 : 2 * π * D.rb y = 2 * √(π * D.vstar y) := by
    rw [mul_assoc, rb, pi_mul_sqrt_div (vstar_pos hY).le]
  rw [h1, h2]
  have h3 : √(π * D.vstar y) ≤ √π :=
    Real.sqrt_le_sqrt (by
      have := hY.vstar_le; have := r0_pos' hY; nlinarith)
  have h4 : √(D.b0 / D.a0 y) ≤ √(D.b0 / D.amin) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hb.le (amin_pos hY) (amin_le_a0 hY))
  have := Real.sqrt_nonneg (D.b0 / D.a0 y)
  have := Real.sqrt_nonneg π
  nlinarith

lemma Amax_ge : max 1 (max |D.A11 y| |D.A22 y|) ≤ 1 + D.Amax := by
  have h1 := abs_A11_le hY
  have h2 := abs_A22_le hY
  have p1 : 0 ≤ √(D.amax / D.b0) / (2 * √(π * D.r0)) := by positivity
  have p2 : 0 ≤ 2 * √π * √(D.b0 / D.amin) := by positivity
  unfold Amax
  refine max_le (by linarith) (max_le (by linarith) (by linarith))

lemma Rdag_pos' : 0 < D.Rdag := Real.sqrt_pos.2 (div_pos (pdag_pos hY.xi_pos hY.L_nonneg)
  Real.pi_pos)

lemma max3_pos' : 0 < max D.Rdag (max D.B3 D.Bstar) := lt_max_of_lt_left (Rdag_pos' hY)

lemma cnew_pos' : 0 < D.cnew :=
  lt_min (by norm_num) (div_pos (by linarith [rbmax_lt_Rh hY.xi_pos hY.L_nonneg (D := D)])
    (by linarith [max3_pos' hY]))

lemma cnew_mul_le' {B : ℝ} (hB : B ≤ max D.Rdag (max D.B3 D.Bstar)) :
    D.cnew * B ≤ (Rh - D.rbmax) / 8 := by
  have hc := cnew_pos' hY
  have hm := max3_pos' hY
  have h1 : D.cnew ≤ (Rh - D.rbmax) / (8 * max D.Rdag (max D.B3 D.Bstar)) := min_le_right _ _
  rw [le_div_iff₀ (by linarith)] at h1
  have : D.cnew * B ≤ D.cnew * max D.Rdag (max D.B3 D.Bstar) :=
    mul_le_mul_of_nonneg_left hB hc.le
  linarith

lemma Amin_sub_pdag_pos : 0 < D.Amin - D.pdag := by
  unfold Amin pdag drect
  have := eta_pos' hY
  nlinarith

lemma Ebar_pos : 1 ≤ D.Ebar := by
  unfold Ebar
  have hE : 0 ≤ D.Erect := by
    unfold Erect drect
    have := hY.M_nonneg; have := kappa_pos' hY; have := eta_pos' hY
    have := nu_pos hY.xi_pos hY.L_nonneg
    have := tol_pos hY.xi_pos
    have : 0 < D.eta / 8 := by linarith
    positivity
  have hK : 0 ≤ D.Kmin := by
    unfold Kmin
    have ha : 0 ≤ D.amin := by unfold amin; positivity
    have hb := hY.b0_pos
    positivity
  have hp := pdag_pos hY.xi_pos hY.L_nonneg
  have hA : 0 ≤ D.Amin := by unfold Amin; positivity
  have := Amin_sub_pdag_pos hY
  have : 0 ≤ D.pdag * D.Amin / (D.Kmin * (D.Amin - D.pdag)) := by positivity
  linarith

lemma dP_pos : 0 < D.dP := by
  unfold dP
  have := Ebar_pos hY; have := hY.M_nonneg; have := kappa_pos' hY
  have := tol_pos hY.xi_pos
  exact div_pos (kappa_pos' hY) (by linarith)

lemma Rq_lt_Rh : D.Rq < Rh := by
  have := dP_pos hY
  unfold Rq Rh
  rw [Real.sqrt_lt_sqrt_iff_of_pos (div_pos one_pos Real.pi_pos)]
  exact div_lt_div_of_pos_right (by linarith) Real.pi_pos

lemma norm_bpt : ‖D.bpt y‖ = D.rb y := by
  rw [bpt, norm_neg, Complex.norm_real]
  exact Real.norm_of_nonneg (by unfold rb; positivity)

lemma Rdag_lt_Rh : D.Rdag < Rh :=
  Real.sqrt_lt_sqrt (div_nonneg (pdag_pos hY.xi_pos hY.L_nonneg).le Real.pi_pos.le)
    (div_lt_div_of_pos_right (pdag_lt_one hY.xi_pos hY.L_nonneg) Real.pi_pos)

lemma Rsupp_lt_Rh : D.Rsupp < Rh := by
  have h1 := Rdag_lt_Rh hY
  have h2 := cnew_mul_le' hY (B := D.B3) ((le_max_left _ _).trans (le_max_right _ _))
  have h3 := cnew_mul_le' hY (B := D.Bstar) ((le_max_right _ _).trans (le_max_right _ _))
  have h4 := Rq_lt_Rh hY
  have h5 := rbmax_lt_Rh hY.xi_pos hY.L_nonneg (D := D)
  exact max_lt (max_lt h1 (by linarith)) (max_lt (by linarith) h4)

lemma Psupp_lt_one : π * D.Rsupp ^ 2 < 1 := by
  have h := Rsupp_lt_Rh hY
  have h0 : 0 ≤ D.Rsupp := (Rdag_pos' hY).le.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hpi := Real.pi_pos
  have hRh : Rh ^ 2 = 1 / π := Real.sq_sqrt (div_nonneg one_pos.le hpi.le)
  have : D.Rsupp ^ 2 < Rh ^ 2 := pow_lt_pow_left₀ h h0 (by norm_num)
  rw [hRh, lt_div_iff₀ hpi] at this
  linarith

/-- `YHyp` gives the hypotheses of the generic five-segment construction. -/
theorem fiveData_hyp : (D.fiveData y).Hyp where
  pdag_pos := pdag_pos hY.xi_pos hY.L_nonneg
  A11_neg := A11_neg hY
  A22_neg := A22_neg hY
  A11_mul_A22 := A11_mul_A22 hY
  smooth := hY.inner.smooth
  q_zero := fun z => by
    show D.qin y 0 z = D.bpt y + (D.fiveData y).A0 z
    rw [FiveData.A0_apply, hY.inner.q_zero z]; rfl
  injOn := hY.inner.injOn
  diff := fun σ hσ z hz => hY.inner.diff σ hσ z hz
  det := fun σ hσ z hz => hY.inner.det σ hσ z hz
  bound := fun σ hσ z hz => hY.inner.bound σ hσ z hz
  bound_one := fun z hz => hY.inner.bound_one z hz
  c_pos := cnew_pos' hY
  c_le_one := by
    show D.cnew ≤ 1
    have : D.cnew ≤ 1 / 4 := min_le_left _ _
    linarith
  B3_ge := by
    show D.Rdag * max 1 (max |D.A11 y| |D.A22 y|) ≤ D.Rdag * (1 + D.Amax)
    exact mul_le_mul_of_nonneg_left (Amax_ge hY) (Rdag_pos' hY).le
  Rdag_le := (le_max_left _ _).trans (le_max_left _ _)
  rbB3_le := by
    show ‖D.bpt y‖ + D.cnew * D.B3 ≤ D.Rsupp
    rw [norm_bpt hY]
    have := rb_le_rbmax hY
    have : D.rbmax + D.cnew * D.B3 ≤ D.Rsupp := (le_max_right _ _).trans (le_max_left _ _)
    linarith
  rbBstar_le := by
    show ‖D.bpt y‖ + D.cnew * D.Bstar ≤ D.Rsupp
    rw [norm_bpt hY]
    have := rb_le_rbmax hY
    have : D.rbmax + D.cnew * D.Bstar ≤ D.Rsupp := (le_max_left _ _).trans (le_max_right _ _)
    linarith
  Rq_le := (le_max_right _ _).trans (le_max_right _ _)
  Psupp_lt_h := Psupp_lt_one hY

/-- **`lem:pln-five-segment` at the parameter `y`.** -/
theorem ordinary_of_yhyp : Qhat.OrdinaryPath (D.pathData y) := by
  rw [pathData_eq_five]
  obtain ⟨he, h4, hp⟩ := pathData_order hY.xi_pos hY.L_nonneg (D := D) y
  exact FiveData.ordinary (fiveData_hyp hY) he h4 hp

end consts

end Input

end SymplecticPacking.HighDim.PlanarGen
