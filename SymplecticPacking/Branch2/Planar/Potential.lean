import SymplecticPacking.Branch2.Comparator.Rearrange

/-!
# The admissible potential pair of a convex profile (`S-sec:plc`, `def:pln-potential-pair`)

Input (`PlanarInput`): a disc capacity `h > 0`, an error `e > 0`, a function `F` continuous,
convex and `L`-Lipschitz on `[0, h]`, and a smooth convex majorant `U₀ : ℝ → ℝ` with
`F ≤ U₀ ≤ F + σ₀` on `[0,h]`, `σ₀ ≤ e/16`.
(For the cubic model `F = K - P_b` and `U₀ = K - H_b + Σ_i softcap_i`, `Model/Unequal.lean`.)

Explicit constants (supplement `sec:plc`):
`η = min(h/16, e/(32(L+1)))/2`, `β = η/(8h)`, `σ = e/8`, `ν = 4σβ(1-β)`, `κ = ση/8`,
`U(P) = U₀(P) + κ(1/P + 1/(h-P))` on `0 < P < h`,
`V(y) = ν y²/(1/4 - y²)` on `|y| < 1/2`.

`U` and `V` are smooth, strictly convex and proper; `U ≥ F`, `V ≥ 0`;
`U ≤ F + σ₀ + σ/4` on `[η, h-η]`, `V ≤ σ` on `|y| ≤ 1/2 - β`. The sublevel estimate (`area_sublevel`)
is estimate (F) of the source: for `0 ≤ I ≤ h - 4η`, the area of
`{(P, y) : U(P) + V(y) ≤ R F(I + 3η) + 2σ}` exceeds `I`, and on this set
`F(P) ≤ R F(I) + 3Lη + 2σ < R F(I) + e`.
-/

noncomputable section

namespace SymplecticPacking.Branch2.Planar

open Set MeasureTheory
open scoped ContDiff

/-- Input of the planar realisation. -/
structure PlanarInput where
  h : ℝ
  e : ℝ
  L : ℝ
  F : ℝ → ℝ
  U0 : ℝ → ℝ
  sig : ℝ

/-- Hypotheses on the planar input. -/
structure PlanarInput.Hyp (D : PlanarInput) : Prop where
  h_pos : 0 < D.h
  e_pos : 0 < D.e
  L_nonneg : 0 ≤ D.L
  F_cont : ContinuousOn D.F (Icc 0 D.h)
  F_convex : ConvexOn ℝ (Icc 0 D.h) D.F
  F_lip : ∀ x ∈ Icc 0 D.h, ∀ y ∈ Icc 0 D.h, |D.F x - D.F y| ≤ D.L * |x - y|
  U0_smooth : ContDiff ℝ ∞ D.U0
  U0_convex : ConvexOn ℝ univ D.U0
  U0_ge : ∀ p ∈ Icc 0 D.h, D.F p ≤ D.U0 p
  U0_le : ∀ p ∈ Icc 0 D.h, D.U0 p ≤ D.F p + D.sig
  sig_nonneg : 0 ≤ D.sig
  sig_le : D.sig ≤ D.e / 16

namespace PlanarInput

variable (D : PlanarInput)

/-- `η = min(h/16, e/(32(L+1)))/2`. -/
def eta : ℝ := min (D.h / 16) (D.e / (32 * (D.L + 1))) / 2

/-- `β = η/(8h)`. -/
def betaY : ℝ := D.eta / (8 * D.h)

/-- `σ = e/8`. -/
def sigma : ℝ := D.e / 8

/-- `ν = 4σβ(1-β)`. -/
def nu : ℝ := 4 * D.sigma * D.betaY * (1 - D.betaY)

/-- `κ = ση/8`. -/
def kappa : ℝ := D.sigma * D.eta / 8

/-- The potential `U(P) = U₀(P) + κ(1/P + 1/(h-P))` (meaningful on `0 < P < h`). -/
def U (P : ℝ) : ℝ := D.U0 P + D.kappa * (1 / P + 1 / (D.h - P))

/-- The angular wall `V(y) = ν y²/(1/4 - y²)` (meaningful on `|y| < 1/2`). -/
def V (y : ℝ) : ℝ := D.nu * y ^ 2 / (1 / 4 - y ^ 2)

variable {D}

lemma Hyp.eta_pos (hD : D.Hyp) : 0 < D.eta := by
  have := hD.h_pos; have := hD.e_pos; have := hD.L_nonneg
  unfold eta; exact half_pos (lt_min (by positivity) (by positivity))

lemma Hyp.eta_le (hD : D.Hyp) : D.eta ≤ D.h / 32 := by
  have := min_le_left (D.h / 16) (D.e / (32 * (D.L + 1)))
  unfold eta; linarith

lemma Hyp.L_mul_eta (hD : D.Hyp) : D.L * D.eta ≤ D.e / 64 := by
  have hL := hD.L_nonneg
  have he := hD.e_pos
  have h1 : D.eta ≤ D.e / (32 * (D.L + 1)) / 2 := by
    have := min_le_right (D.h / 16) (D.e / (32 * (D.L + 1))); unfold eta; linarith
  have h2 : D.L * (D.e / (32 * (D.L + 1)) / 2) ≤ D.e / 64 := by
    rw [show D.L * (D.e / (32 * (D.L + 1)) / 2) = D.e / 64 * (D.L / (D.L + 1)) by
      field_simp; ring]
    have : D.L / (D.L + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  calc D.L * D.eta ≤ D.L * (D.e / (32 * (D.L + 1)) / 2) := mul_le_mul_of_nonneg_left h1 hL
    _ ≤ _ := h2

lemma Hyp.betaY_pos (hD : D.Hyp) : 0 < D.betaY := div_pos hD.eta_pos (by linarith [hD.h_pos])

lemma Hyp.betaY_lt (hD : D.Hyp) : D.betaY < 1 / 2 := by
  have := hD.eta_le; have := hD.h_pos
  unfold betaY; rw [div_lt_iff₀ (by positivity)]; nlinarith

lemma Hyp.kappa_pos (hD : D.Hyp) : 0 < D.kappa := by
  unfold kappa sigma; have := hD.e_pos; have := hD.eta_pos; positivity

lemma Hyp.nu_pos (hD : D.Hyp) : 0 < D.nu := by
  unfold nu sigma; have := hD.e_pos; have := hD.betaY_pos; have := hD.betaY_lt
  have : 0 < 1 - D.betaY := by linarith
  positivity

/-! ### Two elementary strict-convexity inequalities -/

/-- `1/(a x + b y) < a/x + b/y` for `x ≠ y` positive and `a, b > 0`, `a + b = 1`. -/
lemma one_div_strict {x y a b : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) (ha : 0 < a)
    (hb : 0 < b) (hab : a + b = 1) : 1 / (a * x + b * y) < a * (1 / x) + b * (1 / y) := by
  have hz : 0 < a * x + b * y := by positivity
  have hd : 0 < (x - y) ^ 2 := by
    have := sub_ne_zero.2 hxy; positivity
  have key : x * y < (a * x + b * y) * (a * y + b * x) := by
    have hb' : b = 1 - a := by linarith
    subst hb'
    have : 0 < a * (1 - a) * (x - y) ^ 2 := by positivity
    nlinarith
  have e : a * (1 / x) + b * (1 / y) = (a * y + b * x) / (x * y) := by
    field_simp
  rw [e, div_lt_div_iff₀ hz (by positivity)]
  linarith

/-- The barrier `g(t) = 1/(t - c) + 1/(d - t)` is strictly convex on `(c, d)`
(pointwise form). -/
lemma barrier_strict {c d x y a b : ℝ} (hx : x ∈ Ioo c d) (hy : y ∈ Ioo c d) (hxy : x ≠ y)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    1 / (a * x + b * y - c) + 1 / (d - (a * x + b * y)) <
      a * (1 / (x - c) + 1 / (d - x)) + b * (1 / (y - c) + 1 / (d - y)) := by
  have e1 : a * x + b * y - c = a * (x - c) + b * (y - c) := by
    have : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
    linear_combination -this
  have e2 : d - (a * x + b * y) = a * (d - x) + b * (d - y) := by
    have : d = a * d + b * d := by rw [← add_mul, hab, one_mul]
    linear_combination this
  have h1 := one_div_strict (sub_pos.2 hx.1) (sub_pos.2 hy.1)
    (fun h => hxy (by linarith)) ha hb hab
  have h2 := one_div_strict (sub_pos.2 hx.2) (sub_pos.2 hy.2)
    (fun h => hxy (by linarith)) ha hb hab
  rw [e1, e2]
  linarith

/-! ### Properties of the potentials -/

theorem Hyp.U_smooth (hD : D.Hyp) : ContDiffOn ℝ ∞ D.U (Ioo 0 D.h) := by
  unfold U
  apply hD.U0_smooth.contDiffOn.add
  apply contDiffOn_const.mul
  apply ContDiffOn.add
  · exact contDiffOn_const.div contDiffOn_id (fun x hx => hx.1.ne')
  · exact contDiffOn_const.div (contDiffOn_const.sub contDiffOn_id)
      (fun x hx => (sub_pos.2 hx.2).ne')

theorem Hyp.U_strictConvex (hD : D.Hyp) : StrictConvexOn ℝ (Ioo 0 D.h) D.U := by
  have eU : D.U = D.U0 + fun P => D.kappa * (1 / P + 1 / (D.h - P)) := by
    funext P; rfl
  rw [eU]
  refine (hD.U0_convex.subset (subset_univ _) (convex_Ioo _ _)).add_strictConvexOn ?_
  refine ⟨convex_Ioo _ _, fun x hx y hy hxy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  have := barrier_strict (c := 0) hx hy hxy ha hb hab
  simp only [sub_zero] at this
  have hk := hD.kappa_pos
  nlinarith [mul_lt_mul_of_pos_left this hk]

theorem Hyp.U_proper (hD : D.Hyp) :
    Filter.Tendsto D.U (nhdsWithin 0 (Ioi 0)) Filter.atTop ∧
      Filter.Tendsto D.U (nhdsWithin D.h (Iio D.h)) Filter.atTop := by
  have hk := hD.kappa_pos
  have hh := hD.h_pos
  have hU0 := hD.U0_smooth.continuous
  constructor
  · have hc : ContinuousAt (fun P => D.U0 P + D.kappa * (1 / (D.h - P))) 0 := by
      refine hU0.continuousAt.add (continuousAt_const.mul
        (continuousAt_const.div (continuousAt_const.sub continuousAt_id) ?_))
      simp [hh.ne']
    have := (tendsto_inv_nhdsGT_zero.const_mul_atTop hk).atTop_add
      (hc.tendsto.mono_left nhdsWithin_le_nhds)
    refine this.congr (fun P => ?_)
    simp only [U]; ring
  · have hc : ContinuousAt (fun P => D.U0 P + D.kappa * (1 / P)) D.h := by
      refine hU0.continuousAt.add (continuousAt_const.mul
        (continuousAt_const.div continuousAt_id hh.ne'))
    have hsub : Filter.Tendsto (fun P => D.h - P) (nhdsWithin D.h (Iio D.h))
        (nhdsWithin 0 (Ioi 0)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Filter.Tendsto (fun P => D.h - P) (nhds D.h) (nhds (D.h - D.h)) :=
          (continuous_const.sub continuous_id).continuousAt.tendsto
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · exact Filter.mem_of_superset self_mem_nhdsWithin (fun x (hx : x < D.h) => show 0 < D.h - x from sub_pos.2 hx)
    have := ((tendsto_inv_nhdsGT_zero.comp hsub).const_mul_atTop hk).atTop_add
      (hc.tendsto.mono_left nhdsWithin_le_nhds)
    refine this.congr (fun P => ?_)
    simp only [U, Function.comp]; ring

theorem Hyp.U_ge_F (hD : D.Hyp) {P : ℝ} (hP : P ∈ Ioo 0 D.h) : D.F P ≤ D.U P := by
  have h1 := hD.U0_ge P ⟨hP.1.le, hP.2.le⟩
  have hk := hD.kappa_pos
  have hP1 := hP.1
  have hP2 : 0 < D.h - P := sub_pos.2 hP.2
  have : 0 ≤ D.kappa * (1 / P + 1 / (D.h - P)) := by positivity
  unfold U; linarith

/-- `U ≤ F + σ₀ + σ/4` on `[η, h - η]` (the barrier contributes at most `2κ/η = σ/4`).
With `σ₀ ≤ e/16 = σ/2` this gives `U ≤ F + 3σ/4`. -/
theorem Hyp.U_le_F (hD : D.Hyp) {P : ℝ} (hP : P ∈ Icc D.eta (D.h - D.eta)) :
    D.U P ≤ D.F P + D.sig + D.sigma / 4 := by
  have hη := hD.eta_pos
  have hk := hD.kappa_pos
  have hP0 : 0 < P := lt_of_lt_of_le hη hP.1
  have hPh : D.eta ≤ D.h - P := by linarith [hP.2]
  have h1 := hD.U0_le P ⟨hP0.le, by linarith [hP.2]⟩
  have i1 : 1 / P ≤ 1 / D.eta := one_div_le_one_div_of_le hη hP.1
  have i2 : 1 / (D.h - P) ≤ 1 / D.eta := one_div_le_one_div_of_le hη hPh
  have i3 : D.kappa * (1 / P + 1 / (D.h - P)) ≤ D.kappa * (2 / D.eta) := by
    apply mul_le_mul_of_nonneg_left _ hk.le
    rw [show 2 / D.eta = 1 / D.eta + 1 / D.eta by ring]; linarith
  have i4 : D.kappa * (2 / D.eta) = D.sigma / 4 := by
    unfold kappa; field_simp; ring
  unfold U; linarith

theorem Hyp.V_smooth (hD : D.Hyp) : ContDiffOn ℝ ∞ D.V (Ioo (-(1 / 2)) (1 / 2)) := by
  unfold V
  refine (contDiffOn_const.mul (contDiffOn_id.pow 2)).div
    (contDiffOn_const.sub (contDiffOn_id.pow 2)) (fun y hy => ?_)
  have := hy.1; have := hy.2
  have : y ^ 2 < 1 / 4 := by nlinarith
  show (1 : ℝ) / 4 - y ^ 2 ≠ 0
  exact ne_of_gt (by linarith)

theorem Hyp.V_nonneg (hD : D.Hyp) {y : ℝ} (hy : |y| < 1 / 2) : 0 ≤ D.V y := by
  have hy' := abs_lt.1 hy
  have : 0 < 1 / 4 - y ^ 2 := by nlinarith
  unfold V
  exact div_nonneg (mul_nonneg hD.nu_pos.le (sq_nonneg _)) this.le

theorem Hyp.V_le (hD : D.Hyp) {y : ℝ} (hy : |y| ≤ 1 / 2 - D.betaY) : D.V y ≤ D.sigma := by
  have hb0 := hD.betaY_pos
  have hb1 := hD.betaY_lt
  have hs : 0 < D.sigma := by unfold sigma; linarith [hD.e_pos]
  have hy2 : y ^ 2 ≤ (1 / 2 - D.betaY) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg y) hy 2
  set t := D.betaY * (1 - D.betaY) with ht
  have ht0 : 0 < t := by rw [ht]; exact mul_pos hb0 (by linarith)
  have hy2' : y ^ 2 ≤ 1 / 4 - t := by rw [ht]; nlinarith
  have hden : 0 < 1 / 4 - y ^ 2 := by linarith
  have hnu : D.nu = 4 * D.sigma * t := by unfold nu; rw [ht]; ring
  unfold V
  rw [div_le_iff₀ hden, hnu]
  have key : y ^ 2 * (4 * t + 1) ≤ 1 / 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hy2' (by linarith : (0 : ℝ) ≤ 4 * t + 1)]
  nlinarith [mul_le_mul_of_nonneg_left key hs.le]

/-- **Estimate (F) of the source.** For `0 ≤ I ≤ h - 4η`, with `b = R F(I + 3η) + 2σ`, the set
`{(P, y) ∈ (0,h) × (-1/2,1/2) : U(P) + V(y) ≤ b}` has area `> I`, and every point of it has
`F(P) < R F(I) + e`. -/
theorem Hyp.area_sublevel (hD : D.Hyp) {I : ℝ} (hI0 : 0 ≤ I) (hIh : I ≤ D.h - 4 * D.eta) :
    ENNReal.ofReal I < volume {x : ℝ × ℝ | x.1 ∈ Ioo 0 D.h ∧ |x.2| < 1 / 2 ∧
      D.U x.1 + D.V x.2 ≤ Cmp.rearr D.h D.F (I + 3 * D.eta) + 2 * D.sigma} ∧
    ∀ x : ℝ × ℝ, x.1 ∈ Ioo 0 D.h → |x.2| < 1 / 2 →
      D.U x.1 + D.V x.2 ≤ Cmp.rearr D.h D.F (I + 3 * D.eta) + 2 * D.sigma →
      D.F x.1 < Cmp.rearr D.h D.F I + D.e := by
  have hη := hD.eta_pos
  have hh := hD.h_pos
  have he := hD.e_pos
  have hb0 := hD.betaY_pos
  have hb1 := hD.betaY_lt
  have hsig : D.sig ≤ D.sigma / 2 := by have := hD.sig_le; unfold sigma; linarith
  have hσ0 : 0 < D.sigma := by unfold sigma; linarith
  have hJ : I + 3 * D.eta ∈ Icc 0 D.h := ⟨by linarith, by linarith⟩
  constructor
  · obtain ⟨α, hα, hF⟩ := Cmp.rearr_sublevel hD.F_cont hD.F_convex hJ
    set a0 := max α D.eta with ha0
    have ha0l : α ≤ a0 := le_max_left _ _
    have ha0r : D.eta ≤ a0 := le_max_right _ _
    have ha0u : a0 ≤ α + 2 * D.eta := max_le (by linarith) (by linarith [hα.1])
    have ha0h : a0 + (I + D.eta) ≤ D.h - D.eta := by
      rcases le_total α D.eta with h | h
      · rw [ha0, max_eq_right h]; linarith
      · rw [ha0, max_eq_left h]; linarith [hα.2]
    set S : Set (ℝ × ℝ) := Icc a0 (a0 + (I + D.eta)) ×ˢ
      Icc (-(1 / 2 - D.betaY)) (1 / 2 - D.betaY) with hS
    have hsub : S ⊆ {x : ℝ × ℝ | x.1 ∈ Ioo 0 D.h ∧ |x.2| < 1 / 2 ∧
        D.U x.1 + D.V x.2 ≤ Cmp.rearr D.h D.F (I + 3 * D.eta) + 2 * D.sigma} := by
      rintro x ⟨⟨h1, h2⟩, h3, h4⟩
      have hyab : |x.2| ≤ 1 / 2 - D.betaY := abs_le.2 ⟨h3, h4⟩
      refine ⟨⟨by linarith, by linarith⟩, by linarith, ?_⟩
      have hU := hD.U_le_F (P := x.1) ⟨by linarith, by linarith⟩
      have hV := hD.V_le hyab
      have hFx := hF x.1 ⟨by linarith, by linarith⟩
      linarith
    have hvol : volume S = ENNReal.ofReal ((I + D.eta) * (1 - 2 * D.betaY)) := by
      rw [hS, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc,
        ← ENNReal.ofReal_mul (by linarith)]
      congr 1; ring
    have hβh : 2 * D.betaY * D.h = D.eta / 4 := by unfold betaY; field_simp; ring
    have hlt : I < (I + D.eta) * (1 - 2 * D.betaY) := by
      have := mul_le_mul_of_nonneg_left (show I + D.eta ≤ D.h by linarith)
        (by linarith : (0 : ℝ) ≤ 2 * D.betaY)
      nlinarith
    calc ENNReal.ofReal I < ENNReal.ofReal ((I + D.eta) * (1 - 2 * D.betaY)) :=
          (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hlt
      _ = volume S := hvol.symm
      _ ≤ _ := measure_mono hsub
  · intro x hx1 hx2 hle
    have hU := hD.U_ge_F hx1
    have hV := hD.V_nonneg hx2
    have hR := Cmp.rearr_lipschitz hD.F_cont hD.L_nonneg hD.F_lip _ hJ I ⟨hI0, by linarith⟩
    rw [show I + 3 * D.eta - I = 3 * D.eta by ring, abs_of_pos (show (0 : ℝ) < 3 * D.eta by linarith)] at hR
    have hR' := (abs_le.1 (hR)).2
    have hLη := hD.L_mul_eta
    have hσ : D.sigma = D.e / 8 := rfl
    linarith

end PlanarInput

end SymplecticPacking.Branch2.Planar
