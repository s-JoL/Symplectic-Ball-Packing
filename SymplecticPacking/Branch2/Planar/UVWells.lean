import SymplecticPacking.Branch2.Planar.Well
import SymplecticPacking.Branch2.Planar.Potential

/-!
# The two wells of the planar potential pair

For a planar input `D` (`Potential.lean`), the potentials `U` on `(0, h)` and `V` on
`(-1/2, 1/2)` are wells in the sense of `Well.lean`:

* `U` has a unique critical point `p*` (`pstar`, a definite description), which is its minimum;
  `U''(p*) ≥ 2κ(p*⁻³ + (h - p*)⁻³) > 0` since `U₀` is convex;
* `V(y) = νy²/(1/4 - y²)` has `V'(y) = (ν/2) y/(1/4 - y²)²`, `V''(0) = 8ν`.

Both are taken with tolerance `δ = e/64`.
-/

noncomputable section

namespace SymplecticPacking.Branch2.Planar

open Filter Topology Set
open scoped ContDiff Real

namespace PlanarInput

variable (D : PlanarInput)

open Classical in
/-- The critical point `p*` of `U` in `(0, h)` (the unique one, under `Hyp`). -/
def pstar : ℝ :=
  if h : ∃! p, p ∈ Ioo 0 D.h ∧ deriv D.U p = 0 then Explicit.the h else D.h / 2

/-- The tolerance `δ = e/64`. -/
def tol : ℝ := D.e / 64

/-- The `U`-well. -/
def wellU : Well := ⟨D.U, 0, D.h, D.pstar, D.tol⟩

/-- The `V`-well. -/
def wellV : Well := ⟨D.V, -(1 / 2), 1 / 2, 0, D.tol⟩

/-- `dU(P) = U₀'(P) + κ(-(P²)⁻¹ + ((h-P)²)⁻¹)`. -/
def dU (P : ℝ) : ℝ := deriv D.U0 P + D.kappa * (-(P ^ 2)⁻¹ + ((D.h - P) ^ 2)⁻¹)

variable {D}

lemma quarter_sub_pos {y : ℝ} (hy : y ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) : 0 < 1 / 4 - y ^ 2 := by
  have : y ^ 2 < (1 / 2) ^ 2 := by
    rw [← sq_abs]; exact pow_lt_pow_left₀ (abs_lt.mpr hy) (abs_nonneg _) (by norm_num)
  linarith

lemma hasDerivAt_V {y : ℝ} (hy : 1 / 4 - y ^ 2 ≠ 0) :
    HasDerivAt D.V (D.nu * (y / 2) / (1 / 4 - y ^ 2) ^ 2) y := by
  have h1 : HasDerivAt (fun y : ℝ => D.nu * y ^ 2) (D.nu * (2 * y)) y :=
    ((hasDerivAt_pow 2 y).const_mul D.nu).congr_deriv (by norm_num)
  have h2 : HasDerivAt (fun y : ℝ => 1 / 4 - y ^ 2) (-(2 * y)) y :=
    ((hasDerivAt_pow 2 y).const_sub (1 / 4)).congr_deriv (by norm_num)
  have := h1.div h2 hy
  refine this.congr_deriv ?_
  field_simp
  ring

lemma V_zero : D.V 0 = 0 := by simp [V]

section hyp
variable (hD : D.Hyp)
include hD

lemma U_contDiffAt {p : ℝ} (hp : p ∈ Ioo 0 D.h) : ContDiffAt ℝ ∞ D.U p :=
  hD.U_smooth.contDiffAt (isOpen_Ioo.mem_nhds hp)

lemma U_diffAt {p : ℝ} (hp : p ∈ Ioo 0 D.h) : DifferentiableAt ℝ D.U p :=
  (U_contDiffAt hD hp).differentiableAt (by simp)

lemma deriv_U_strictMonoOn : StrictMonoOn (deriv D.U) (Ioo 0 D.h) :=
  hD.U_strictConvex.strictMonoOn_deriv fun _ hx => U_diffAt hD hx

lemma U_continuousOn : ContinuousOn D.U (Ioo 0 D.h) := hD.U_smooth.continuousOn

theorem exists_min : ∃ p ∈ Ioo 0 D.h, ∀ q ∈ Ioo 0 D.h, D.U p ≤ D.U q := by
  have hh := hD.h_pos
  set c := D.h / 2
  have hc : c ∈ Ioo 0 D.h := ⟨by positivity, by simp only [c]; linarith⟩
  obtain ⟨hl, hr⟩ := hD.U_proper
  have e1 : {x | D.U c < D.U x} ∈ 𝓝[>] (0 : ℝ) := hl (eventually_gt_atTop _)
  have e2 : {x | D.U c < D.U x} ∈ 𝓝[<] D.h := hr (eventually_gt_atTop _)
  obtain ⟨a₁, ha₁, hsub1⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp e1
  obtain ⟨b₁, hb₁, hsub2⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).mp e2
  simp only [mem_Ioi] at ha₁
  simp only [mem_Iio] at hb₁
  set a := min (a₁ / 2) (c / 2)
  set b := max ((b₁ + D.h) / 2) ((c + D.h) / 2)
  have ha0 : 0 < a := lt_min (by linarith) (by simp only [c]; linarith)
  have hac : a < c := (min_le_right _ _).trans_lt (by simp only [c]; linarith)
  have haa : a < a₁ := (min_le_left _ _).trans_lt (by linarith)
  have hcb : c < b := lt_of_lt_of_le (by simp only [c]; linarith) (le_max_right _ _)
  have hbh : b < D.h := max_lt (by linarith) (by simp only [c]; linarith)
  have hbb : b₁ < b := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hsub : Icc a b ⊆ Ioo 0 D.h := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨p, hp, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨c, hac.le, hcb.le⟩
    ((U_continuousOn hD).mono hsub)
  refine ⟨p, hsub hp, fun q hq => ?_⟩
  have hpc : D.U p ≤ D.U c := hmin ⟨hac.le, hcb.le⟩
  by_cases hqa : q < a
  · have := hsub1 ⟨hq.1, by linarith⟩; simp only [mem_setOf_eq] at this; linarith
  by_cases hqb : b < q
  · have := hsub2 ⟨by linarith, hq.2⟩; simp only [mem_setOf_eq] at this; linarith
  exact hmin ⟨not_lt.mp hqa, not_lt.mp hqb⟩

theorem exists_unique_crit : ∃! p, p ∈ Ioo 0 D.h ∧ deriv D.U p = 0 := by
  obtain ⟨p, hp, hmin⟩ := exists_min hD
  have hloc : IsLocalMin D.U p := by
    filter_upwards [isOpen_Ioo.mem_nhds hp] with q hq using hmin q hq
  refine ⟨p, ⟨hp, hloc.deriv_eq_zero⟩, fun q ⟨hq, hq0⟩ => ?_⟩
  exact (deriv_U_strictMonoOn hD).injOn hq hp (by rw [hq0, hloc.deriv_eq_zero])

theorem pstar_spec : D.pstar ∈ Ioo 0 D.h ∧ deriv D.U D.pstar = 0 := by
  have h := exists_unique_crit hD
  unfold pstar
  rw [dif_pos h]
  exact Explicit.the_spec h

lemma pstar_mem : D.pstar ∈ Ioo 0 D.h := (pstar_spec hD).1

theorem pstar_isMin {q : ℝ} (hq : q ∈ Ioo 0 D.h) : D.U D.pstar ≤ D.U q := by
  obtain ⟨p, hp, hmin⟩ := exists_min hD
  have hloc : IsLocalMin D.U p := by
    filter_upwards [isOpen_Ioo.mem_nhds hp] with q hq using hmin q hq
  have : D.pstar = p := (exists_unique_crit hD).unique (pstar_spec hD) ⟨hp, hloc.deriv_eq_zero⟩
  rw [this]; exact hmin q hq

theorem U_sign {x : ℝ} (hx : x ∈ Ioo 0 D.h) (hne : x ≠ D.pstar) :
    0 < (x - D.pstar) * deriv D.U x := by
  have h0 := (pstar_spec hD).2
  have hm := deriv_U_strictMonoOn hD
  rcases lt_or_gt_of_ne hne with h | h
  · have := hm hx (pstar_mem hD) h
    rw [h0] at this
    exact mul_pos_of_neg_of_neg (by linarith) this
  · have := hm (pstar_mem hD) hx h
    rw [h0] at this
    exact mul_pos (by linarith) this

lemma hasDerivAt_wall {P : ℝ} (hP : P ∈ Ioo 0 D.h) :
    HasDerivAt (fun P => D.kappa * (1 / P + 1 / (D.h - P)))
      (D.kappa * (-(P ^ 2)⁻¹ + ((D.h - P) ^ 2)⁻¹)) P := by
  have h1 : HasDerivAt (fun P : ℝ => 1 / P) (-(P ^ 2)⁻¹) P := by
    simpa [one_div] using hasDerivAt_inv (ne_of_gt hP.1)
  have hhp : D.h - P ≠ 0 := by linarith [hP.2]
  have h2 : HasDerivAt (fun P : ℝ => 1 / (D.h - P)) ((D.h - P) ^ 2)⁻¹ P := by
    have := ((hasDerivAt_id' P).const_sub D.h).inv hhp
    simp only [one_div]
    exact this.congr_deriv (by rw [neg_neg, one_div])
  exact (h1.add h2).const_mul D.kappa

lemma hasDerivAt_U {P : ℝ} (hP : P ∈ Ioo 0 D.h) : HasDerivAt D.U (D.dU P) P := by
  have h0 : HasDerivAt D.U0 (deriv D.U0 P) P :=
    (hD.U0_smooth.differentiable (by simp) P).hasDerivAt
  exact h0.add (hasDerivAt_wall hD hP)

lemma deriv_U_eventually : deriv D.U =ᶠ[𝓝 D.pstar] D.dU := by
  filter_upwards [isOpen_Ioo.mem_nhds (pstar_mem hD)] with P hP
  exact (hasDerivAt_U hD hP).deriv

theorem U_second_pos : 0 < deriv (deriv D.U) D.pstar := by
  rw [(deriv_U_eventually hD).deriv_eq]
  have hp := pstar_mem hD
  set P := D.pstar
  have hP0 : P ≠ 0 := ne_of_gt hp.1
  have hhp : D.h - P ≠ 0 := by linarith [hp.2]
  have hU0' : ContDiff ℝ ∞ (deriv D.U0) := (contDiff_infty_iff_deriv.mp hD.U0_smooth).2
  have d0 : HasDerivAt (deriv D.U0) (deriv (deriv D.U0) P) P :=
    (hU0'.differentiable (by simp) P).hasDerivAt
  have d1 : HasDerivAt (fun P : ℝ => -(P ^ 2)⁻¹) (-(-(2 * P) / (P ^ 2) ^ 2)) P := by
    have hp2 : HasDerivAt (fun P : ℝ => P ^ 2) (2 * P) P :=
      (hasDerivAt_pow 2 P).congr_deriv (by norm_num)
    exact (hp2.inv (pow_ne_zero 2 hP0)).neg
  have d2 : HasDerivAt (fun P : ℝ => ((D.h - P) ^ 2)⁻¹)
      (-(2 * (D.h - P) * (-1)) / ((D.h - P) ^ 2) ^ 2) P := by
    have hq : HasDerivAt (fun P : ℝ => (D.h - P) ^ 2) (2 * (D.h - P) * (-1)) P :=
      (((hasDerivAt_id' P).const_sub D.h).pow 2).congr_deriv (by norm_num)
    exact hq.inv (pow_ne_zero 2 hhp)
  have hd := d0.add ((d1.add d2).const_mul D.kappa)
  have hdd : deriv (fun P => deriv D.U0 P + D.kappa * (-(P ^ 2)⁻¹ + ((D.h - P) ^ 2)⁻¹)) P =
      deriv (deriv D.U0) P + D.kappa * (-(-(2 * P) / (P ^ 2) ^ 2) +
        -(2 * (D.h - P) * (-1)) / ((D.h - P) ^ 2) ^ 2) := hd.deriv
  rw [show D.dU = fun P => deriv D.U0 P + D.kappa * (-(P ^ 2)⁻¹ + ((D.h - P) ^ 2)⁻¹) from rfl,
    hdd]
  have hmono : Monotone (deriv D.U0) := by
    have := hD.U0_convex.monotoneOn_deriv
      (fun x _ => hD.U0_smooth.differentiable (by simp) x)
    exact fun x y hxy => this (mem_univ x) (mem_univ y) hxy
  have hU2 : 0 ≤ deriv (deriv D.U0) P := hmono.deriv_nonneg
  have hk := hD.kappa_pos
  have hPpos : 0 < P := hp.1
  have hhpos : 0 < D.h - P := by linarith [hp.2]
  have t1 : 0 < -(-(2 * P) / (P ^ 2) ^ 2) := by
    rw [neg_div, neg_neg]; positivity
  have t2 : 0 < -(2 * (D.h - P) * (-1)) / ((D.h - P) ^ 2) ^ 2 := by
    rw [show -(2 * (D.h - P) * (-1)) = 2 * (D.h - P) by ring]; positivity
  have := mul_pos hk (add_pos t1 t2)
  linarith

theorem wellU_hyp : D.wellU.Hyp where
  A_lt := (pstar_mem hD).1
  lt_B := (pstar_mem hD).2
  δ_pos := by show 0 < D.e / 64; linarith [hD.e_pos]
  smooth := hD.U_smooth
  crit := (pstar_spec hD).2
  sign := fun x hx hne => U_sign hD hx hne
  second := U_second_pos hD
  top := hD.U_proper.2
  bot := hD.U_proper.1

/-! ### The `V`-well -/

theorem V_second_pos : 0 < deriv (deriv D.V) 0 := by
  have hev : deriv D.V =ᶠ[𝓝 0] fun y => D.nu * (y / 2) / (1 / 4 - y ^ 2) ^ 2 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show (0 : ℝ) ∈ Ioo (-(1 / 2)) (1 / 2) by norm_num)]
      with y hy
    exact (hasDerivAt_V (D := D) (quarter_sub_pos hy).ne').deriv
  rw [hev.deriv_eq]
  have hn : HasDerivAt (fun y : ℝ => D.nu * (y / 2)) (D.nu * (1 / 2)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).div_const 2).const_mul D.nu
  have hq : HasDerivAt (fun y : ℝ => (1 / 4 - y ^ 2) ^ 2) 0 0 :=
    (((hasDerivAt_pow 2 (0 : ℝ)).const_sub (1 / 4)).pow 2).congr_deriv (by norm_num)
  have hd := hn.div hq (by norm_num)
  have hdd : deriv (fun y : ℝ => D.nu * (y / 2) / (1 / 4 - y ^ 2) ^ 2) 0 =
      (D.nu * (1 / 2) * (1 / 4 - 0 ^ 2) ^ 2 - D.nu * (0 / 2) * 0) / ((1 / 4 - 0 ^ 2) ^ 2) ^ 2 :=
    hd.deriv
  rw [hdd]
  have := hD.nu_pos
  norm_num
  positivity

theorem V_tendsto_top : Tendsto D.V (𝓝[<] (1 / 2)) atTop := by
  have hν := hD.nu_pos
  have h1 : Tendsto (fun y : ℝ => D.nu * y ^ 2) (𝓝[<] (1 / 2)) (𝓝 (D.nu * (1 / 2) ^ 2)) :=
    ((continuous_const.mul (continuous_pow 2)).tendsto _).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun y : ℝ => 1 / 4 - y ^ 2) (𝓝[<] (1 / 2)) (𝓝[>] 0) := by
    have hc : Tendsto (fun y : ℝ => 1 / 4 - y ^ 2) (𝓝 (1 / 2)) (𝓝 (1 / 4 - (1 / 2) ^ 2)) :=
      (continuous_const.sub (continuous_pow 2)).tendsto _
    norm_num at hc
    refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
    exact quarter_sub_pos ⟨by linarith [hy.1], hy.2⟩
  have := h1.pos_mul_atTop (by positivity) h2.inv_tendsto_nhdsGT_zero
  refine this.congr' (Eventually.of_forall fun y => ?_)
  simp [V, div_eq_mul_inv]

theorem V_tendsto_bot : Tendsto D.V (𝓝[>] (-(1 / 2))) atTop := by
  have hν := hD.nu_pos
  have h1 : Tendsto (fun y : ℝ => D.nu * y ^ 2) (𝓝[>] (-(1 / 2))) (𝓝 (D.nu * (-(1 / 2)) ^ 2)) :=
    ((continuous_const.mul (continuous_pow 2)).tendsto _).mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun y : ℝ => 1 / 4 - y ^ 2) (𝓝[>] (-(1 / 2))) (𝓝[>] 0) := by
    have hc : Tendsto (fun y : ℝ => 1 / 4 - y ^ 2) (𝓝 (-(1 / 2))) (𝓝 (1 / 4 - (-(1 / 2)) ^ 2)) :=
      (continuous_const.sub (continuous_pow 2)).tendsto _
    norm_num at hc
    refine tendsto_nhdsWithin_iff.mpr ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (show (-(1 / 2) : ℝ) < 0 by norm_num)] with y hy
    exact quarter_sub_pos ⟨hy.1, by linarith [hy.2]⟩
  have := h1.pos_mul_atTop (by positivity) h2.inv_tendsto_nhdsGT_zero
  refine this.congr' (Eventually.of_forall fun y => ?_)
  simp [V, div_eq_mul_inv]

theorem wellV_hyp : D.wellV.Hyp where
  A_lt := by show (-(1 / 2) : ℝ) < 0; norm_num
  lt_B := by show (0 : ℝ) < 1 / 2; norm_num
  δ_pos := by show 0 < D.e / 64; linarith [hD.e_pos]
  smooth := hD.V_smooth
  crit := by
    show deriv D.V 0 = 0
    rw [(hasDerivAt_V (D := D) (by norm_num)).deriv]; simp
  sign := fun x hx hne => by
    show 0 < (x - 0) * deriv D.V x
    have hq := quarter_sub_pos hx
    rw [(hasDerivAt_V (D := D) hq.ne').deriv, sub_zero]
    have := hD.nu_pos
    have hx2 : 0 < x ^ 2 := lt_of_le_of_ne (sq_nonneg x) (Ne.symm (pow_ne_zero 2 hne))
    have : x * (D.nu * (x / 2) / (1 / 4 - x ^ 2) ^ 2) = D.nu * x ^ 2 / (2 * (1 / 4 - x ^ 2) ^ 2) := by
      field_simp
    rw [this]; positivity
  second := V_second_pos hD
  top := V_tendsto_top hD
  bot := V_tendsto_bot hD

lemma V_nonneg' {y : ℝ} (hy : y ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) : 0 ≤ D.V y := by
  have := quarter_sub_pos hy; have := hD.nu_pos
  unfold V; positivity

end hyp

end PlanarInput

end SymplecticPacking.Branch2.Planar
