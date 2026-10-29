import SymplecticPacking.Strip.Morse
import SymplecticPacking.Strip.Normalize

/-!
# The strip map

`sec:str` (paper `cons:str-map`, `lem:str-area` (iii), (iv), `prop:str-strip`): the strip map
`Ψ_strip = F_st ∘ T_st⁻¹ ∘ D_st : ℂ → (0, ∞) × (0, 1)`, its area preservation and the strip
estimate `0 < x < π|z|² + δ/2`.

Points of the strip are complex numbers `x + iT`. Smoothness: the paper proves that `Ψ_strip`
is real-analytic; here `C^∞` suffices and is proved (`psiStrip_smooth`) by the general
normalisation lemma `normalize_general` (`Strip/Normalize.lean`), which needs neither
analyticity nor flatness of the density.
-/

noncomputable section

namespace SymplecticPacking.Strip

open Filter Topology Set Metric MeasureTheory
open scoped ContDiff Real

set_option linter.unusedSectionVars false

/-! ### Definitions (`cons:str-map`) -/

/-- `F_st(u + iv) = X_st(u) + i Y_st(v)`. -/
def Fst (b : ℝ) (w : ℂ) : ℂ := ⟨Xst b w.re, Yst b w.im⟩

/-- The density `J_st(u + iv) = X_st'(u) Y_st'(v)`. -/
def Jst (b : ℝ) (w : ℂ) : ℝ := XstD b w.re * YstD b w.im

/-- `𝓐_st(E) = π ∫₀^E J̄_st` (`= ∫_{|ϖ|² ≤ E} J_st`, `Ast_eq_integral`). -/
def Ast (b E : ℝ) : ℝ := Inner.Acal (cf (Jst b)) 0 E

/-- `E_st = 𝓐_st⁻¹`. -/
def Est (b : ℝ) (I : ℝ) : ℝ := Inner.Einv (cf (Jst b)) 0 I

/-- The strip map `Ψ_strip = F_st ∘ T_st⁻¹ ∘ D_st` (`b_st = δ/π`). -/
def psiStrip (δ : ℝ) (z : ℂ) : ℂ :=
  Fst (bst δ) (Inner.TrotInv (cf (Jst (bst δ))) 0 (Inner.Darea (cf (Jst (bst δ))) 0 z))

section
variable {b : ℝ} (hb : 0 < b)
include hb

/-! ### `F_st` and `J_st` -/

theorem Fst_eq (w : ℂ) : Fst b w = (Xst b w.re : ℂ) + (Yst b w.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [Fst]

theorem Fst_contDiff : ContDiff ℝ ∞ (Fst b) := by
  have : Fst b = fun w => (Xst b w.re : ℂ) + (Yst b w.im : ℂ) * Complex.I :=
    funext (Fst_eq hb)
  rw [this]
  exact (Complex.ofRealCLM.contDiff.comp ((contDiff_Xst hb).comp Complex.reCLM.contDiff)).add
    ((Complex.ofRealCLM.contDiff.comp ((contDiff_Yst hb).comp Complex.imCLM.contDiff)).mul
      contDiff_const)

theorem Jst_contDiff : ContDiff ℝ ∞ (Jst b) :=
  ((contDiff_XstD hb).comp Complex.reCLM.contDiff).mul
    ((contDiff_YstD hb).comp Complex.imCLM.contDiff)

theorem Jst_pos (w : ℂ) : 0 < Jst b w := mul_pos (XstD_pos hb _) (YstD_pos hb _)

theorem Fst_line (w v : ℂ) :
    HasDerivAt (fun t : ℝ => Fst b (w + t • v))
      ((XstD b w.re * v.re : ℝ) + (YstD b w.im * v.im : ℝ) * Complex.I) 0 := by
  have hx : HasDerivAt (fun t : ℝ => w.re + t * v.re) v.re 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.re).const_add w.re
  have hy : HasDerivAt (fun t : ℝ => w.im + t * v.im) v.im 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const v.im).const_add w.im
  have hX : HasDerivAt (fun t : ℝ => Xst b (w.re + t * v.re)) (XstD b w.re * v.re) 0 := by
    exact (deriv_Xst hb w.re).comp_of_eq 0 hx (by simp)
  have hY : HasDerivAt (fun t : ℝ => Yst b (w.im + t * v.im)) (YstD b w.im * v.im) 0 := by
    exact (deriv_Yst hb w.im).comp_of_eq 0 hy (by simp)
  have h := hX.ofReal_comp.add (hY.ofReal_comp.mul_const Complex.I)
  convert h using 1
  funext t
  rw [Fst_eq hb]
  simp

theorem fderiv_Fst_apply (w v : ℂ) :
    fderiv ℝ (Fst b) w v = (XstD b w.re * v.re : ℝ) + (YstD b w.im * v.im : ℝ) * Complex.I := by
  have hd : DifferentiableAt ℝ (Fst b) w := (Fst_contDiff hb).differentiable (by simp) w
  have hl : HasDerivAt (fun t : ℝ => w + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add w
  have h0 : HasFDerivAt (Fst b) (fderiv ℝ (Fst b) w) (w + (0 : ℝ) • v) := by
    simpa using hd.hasFDerivAt
  exact (h0.comp_hasDerivAt (l := Fst b) (0 : ℝ) hl).unique (Fst_line hb w v)

/-- `F_st^*(dx ∧ dT) = J_st du ∧ dv`. -/
theorem Fst_det (w : ℂ) : LinearMap.det (fderiv ℝ (Fst b) w : ℂ →ₗ[ℝ] ℂ) = Jst b w := by
  rw [← Qhat.det2_eq, Qhat.det2, fderiv_Fst_apply hb, fderiv_Fst_apply hb]
  simp [Jst]

theorem Fst_bijOn : BijOn (Fst b) univ {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ z.im < 1} := by
  refine ⟨fun w _ => ⟨Xst_pos hb _, (Yst_mem hb _).1, (Yst_mem hb _).2⟩, ?_, ?_⟩
  · intro w₁ _ w₂ _ h
    have h1 : Xst b w₁.re = Xst b w₂.re := congrArg Complex.re h
    have h2 : Yst b w₁.im = Yst b w₂.im := congrArg Complex.im h
    exact Complex.ext ((Xst_strictMono hb).injective h1) ((Yst_strictMono hb).injective h2)
  · rintro z ⟨h1, h2, h3⟩
    obtain ⟨u, -, hu⟩ := (Xst_bijOn hb).2.2 (show z.re ∈ Ioi (0 : ℝ) from h1)
    obtain ⟨v, -, hv⟩ := (Yst_bijOn hb).2.2 (show z.im ∈ Ioo (0 : ℝ) 1 from ⟨h2, h3⟩)
    exact ⟨⟨u, v⟩, mem_univ _, Complex.ext (by simp [Fst, hu]) (by simp [Fst, hv])⟩

/-- `R_st ∘ X_st + V_st ∘ Y_st = u² + v²`. -/
theorem level_Fst (w : ℂ) : Rst b (Fst b w).re + Vst b (Fst b w).im = ‖w‖ ^ 2 := by
  simp only [Fst, Rst_Xst hb, Vst_Yst hb]
  rw [Complex.sq_norm, Complex.normSq_apply]; ring

/-! ### `𝓐_st` as an area integral; the lower bound (`lem:str-area` (iii)) -/

/-- `𝓐_st(E) = ∫_{|ϖ|² ≤ E} J_st`. -/
theorem Ast_eq_integral {E : ℝ} (hE : 0 ≤ E) :
    Ast b E = ∫ w in closedBall (0 : ℂ) (Real.sqrt E), Jst b w := by
  rw [Qhat.integral_closedBall_eq_Acal (Jst_contDiff hb).continuous (Real.sqrt_nonneg E),
    Real.sq_sqrt hE]
  rfl

theorem Xst_sub_neg (s : ℝ) : Xst b s - Xst b (-s) = s * Real.sqrt (s ^ 2 + 2 * b) := by
  unfold Xst; rw [neg_sq]; ring

/-- Fubini: `∫_{|ϖ|² ≤ E} J_st = ∫_{-√E}^{√E} Y'(v) [X(√(E - v²)) - X(-√(E - v²))] dv`. -/
theorem integral_disk_Jst {E : ℝ} (hE : 0 ≤ E) :
    ∫ w in closedBall (0 : ℂ) (Real.sqrt E), Jst b w =
      ∫ v in (-Real.sqrt E)..(Real.sqrt E), YstD b v *
        (Xst b (Real.sqrt (E - v ^ 2)) - Xst b (-Real.sqrt (E - v ^ 2))) := by
  set ρ := Real.sqrt E
  have hρ : 0 ≤ ρ := Real.sqrt_nonneg E
  have hρ2 : ρ ^ 2 = E := Real.sq_sqrt hE
  set K : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 ≤ E}
  set g : ℝ × ℝ → ℝ := fun p => XstD b p.1 * YstD b p.2
  have hgc : Continuous g :=
    ((contDiff_XstD hb).continuous.comp continuous_fst).mul
      ((contDiff_YstD hb).continuous.comp continuous_snd)
  have hKc : IsClosed K := isClosed_le (by fun_prop) continuous_const
  have hsq : ∀ x : ℝ, x ^ 2 ≤ E → x ∈ Icc (-ρ) ρ := fun x hx => abs_le.mp (Real.abs_le_sqrt hx)
  have hKsub : K ⊆ Icc (-ρ) ρ ×ˢ Icc (-ρ) ρ := fun p hp => by
    have : p.1 ^ 2 + p.2 ^ 2 ≤ E := hp
    exact ⟨hsq _ (by nlinarith [sq_nonneg p.2]), hsq _ (by nlinarith [sq_nonneg p.1])⟩
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hKc hKsub
  have hint : Integrable (K.indicator g) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (hgc.continuousOn.integrableOn_compact hK).integrable_indicator hKc.measurableSet
  -- to the product
  have h1 : ∫ w in closedBall (0 : ℂ) ρ, Jst b w = ∫ p : ℝ × ℝ, K.indicator g p := by
    rw [← integral_indicator measurableSet_closedBall,
      ← Complex.volume_preserving_equiv_real_prod.integral_comp' (K.indicator g)]
    congr 1
    funext w
    simp only [Complex.measurableEquivRealProd_apply]
    have hiff : w ∈ closedBall (0 : ℂ) ρ ↔ (w.re, w.im) ∈ K := by
      rw [mem_closedBall_zero_iff]
      show ‖w‖ ≤ ρ ↔ w.re ^ 2 + w.im ^ 2 ≤ E
      rw [← hρ2, ← sq_le_sq₀ (norm_nonneg w) hρ, Complex.sq_norm, Complex.normSq_apply]
      constructor <;> intro h <;> nlinarith
    by_cases hw : w ∈ closedBall (0 : ℂ) ρ
    · rw [indicator_of_mem hw, indicator_of_mem (hiff.mp hw)]; rfl
    · rw [indicator_of_notMem hw, indicator_of_notMem (fun h => hw (hiff.mpr h))]
  -- Fubini
  rw [h1, Measure.volume_eq_prod, integral_prod_symm _ hint]
  -- the inner integrals
  have h2 : ∀ v : ℝ, ∫ u, K.indicator g (u, v) = (Icc (-ρ) ρ).indicator
      (fun v => YstD b v * (Xst b (Real.sqrt (E - v ^ 2)) - Xst b (-Real.sqrt (E - v ^ 2)))) v := by
    intro v
    by_cases hv : v ^ 2 ≤ E
    · rw [indicator_of_mem (hsq v hv)]
      set s := Real.sqrt (E - v ^ 2)
      have hs : 0 ≤ s := Real.sqrt_nonneg _
      have hs2 : s ^ 2 = E - v ^ 2 := Real.sq_sqrt (by linarith)
      have he : (fun u => K.indicator g (u, v)) = (Icc (-s) s).indicator (fun u => XstD b u * YstD b v) := by
        funext u
        have hiff : (u, v) ∈ K ↔ u ∈ Icc (-s) s := by
          show u ^ 2 + v ^ 2 ≤ E ↔ _
          constructor
          · intro h; exact abs_le.mp (Real.abs_le_sqrt (by linarith))
          · intro h
            have := sq_le_sq' h.1 h.2
            linarith
        by_cases hu : u ∈ Icc (-s) s
        · rw [indicator_of_mem hu, indicator_of_mem (hiff.mpr hu)]
        · rw [indicator_of_notMem hu, indicator_of_notMem (fun h => hu (hiff.mp h))]
      rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_mul_const,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => deriv_Xst hb x)
          ((contDiff_XstD hb).continuous.intervalIntegrable _ _)]
      ring
    · push Not at hv
      have hnot : v ∉ Icc (-ρ) ρ := fun h => by
        have := sq_le_sq' h.1 h.2; linarith
      rw [indicator_of_notMem hnot]
      have : (fun u => K.indicator g (u, v)) = fun _ => 0 := by
        funext u
        apply indicator_of_notMem
        show ¬ (u ^ 2 + v ^ 2 ≤ E)
        nlinarith [sq_nonneg u]
      rw [this, integral_zero]
  simp_rw [h2]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]

/-- An antiderivative of `v ↦ Y'(v) (E - v²)`: `(E + b) Y(v) - (b/2) arcsin φ(v)`. -/
def Hst (b E v : ℝ) : ℝ := (E + b) * Yst b v - b / 2 * Real.arcsin (phiSt b v)

theorem phiSt_eq (v : ℝ) : phiSt b v = 2 * Yst b v - 1 := by rw [Yst_eq_phi]; ring

theorem phiSt_neg (v : ℝ) : phiSt b (-v) = -phiSt b v := by
  unfold phiSt; rw [neg_sq]; ring

theorem Hst_hasDerivAt (E v : ℝ) : HasDerivAt (Hst b E) (YstD b v * (E - v ^ 2)) v := by
  have hφ : HasDerivAt (phiSt b) (2 * YstD b v) v := by
    have := ((deriv_Yst hb v).const_mul 2).sub_const 1
    convert this using 1
    funext x; exact phiSt_eq hb x
  have hab := abs_lt.mp (abs_phiSt_lt hb v)
  have ha := (Real.hasDerivAt_arcsin (x := phiSt b v) (by linarith) (by linarith)).comp v hφ
  have h := ((deriv_Yst hb v).const_mul (E + b)).sub (ha.const_mul (b / 2))
  convert h using 1
  · funext x; simp [Hst]
  · rw [sqrt_one_sub_phiSt_sq hb]
    have : 0 < v ^ 2 + b := by positivity
    field_simp
    ring

/-- The elementary bound `(E + b) φ - b arcsin φ ≥ E - b(π/2 - 1)` at `φ = φ(√E)`. -/
theorem Hst_bound {E : ℝ} (hE : 0 ≤ E) :
    E - b * (π / 2 - 1) ≤ Hst b E (Real.sqrt E) - Hst b E (-Real.sqrt E) := by
  set ρ := Real.sqrt E
  have hρ2 : ρ ^ 2 = E := Real.sq_sqrt hE
  set φ := phiSt b ρ
  have hYn : Yst b (-ρ) = 1 - Yst b ρ := by
    have h1 := phiSt_eq hb (-ρ); have h2 := phiSt_eq hb ρ; rw [phiSt_neg hb] at h1; linarith
  have hH : Hst b E ρ - Hst b E (-ρ) = (E + b) * φ - b * Real.arcsin φ := by
    unfold Hst
    rw [hYn, phiSt_neg hb, Real.arcsin_neg, Yst_eq_phi]
    ring
  rw [hH]
  set m := E + b
  have hm : 0 < m := by positivity
  have hφ2 : φ ^ 2 = 1 - (b / m) ^ 2 := by
    have := phiSt_sq hb ρ; rw [hρ2] at this; exact this
  have hφ0 : 0 ≤ φ := by
    unfold φ phiSt; have := Real.sqrt_nonneg E; positivity
  have hφ1 : φ ≤ 1 := (abs_lt.mp (abs_phiSt_lt hb ρ)).2.le
  have hac : b / m ≤ Real.arccos φ := by
    have h := Real.sin_le (Real.arccos_nonneg φ)
    rw [Real.sin_arccos, hφ2, sub_sub_cancel, Real.sqrt_sq (by positivity)] at h
    exact h
  rw [Real.arcsin_eq_pi_div_two_sub_arccos]
  have h1 : m * (1 - φ) ≤ m * (1 - φ ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hm.le; nlinarith
  have h2 : m * (1 - φ ^ 2) = b * (b / m) := by rw [hφ2]; field_simp; ring
  have h3 : b * (b / m) ≤ b * Real.arccos φ := mul_le_mul_of_nonneg_left hac hb.le
  simp only [m] at *
  nlinarith

/-- **`lem:str-area` (iii).** `𝓐_st(E) ≥ E - b(π/2 - 1)` for `E ≥ 0`. -/
theorem Ast_ge {E : ℝ} (hE : 0 ≤ E) : E - b * (π / 2 - 1) ≤ Ast b E := by
  set ρ := Real.sqrt E
  have hρ : 0 ≤ ρ := Real.sqrt_nonneg E
  have hρ2 : ρ ^ 2 = E := Real.sq_sqrt hE
  rw [Ast_eq_integral hb hE, integral_disk_Jst hb hE]
  have hlow : ∫ v in (-ρ)..ρ, YstD b v * (E - v ^ 2) = Hst b E ρ - Hst b E (-ρ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => Hst_hasDerivAt hb E v)
      (((contDiff_YstD hb).continuous.mul (by fun_prop)).intervalIntegrable _ _)
  have hmono : ∫ v in (-ρ)..ρ, YstD b v * (E - v ^ 2) ≤
      ∫ v in (-ρ)..ρ, YstD b v * (Xst b (Real.sqrt (E - v ^ 2)) - Xst b (-Real.sqrt (E - v ^ 2))) := by
    have hXc := (contDiff_Xst hb).continuous
    apply intervalIntegral.integral_mono_on (by linarith)
    · exact ((contDiff_YstD hb).continuous.mul (by fun_prop)).intervalIntegrable _ _
    · exact ((contDiff_YstD hb).continuous.mul ((hXc.comp (by fun_prop)).sub
        (hXc.comp (by fun_prop)))).intervalIntegrable _ _
    · intro v hv
      apply mul_le_mul_of_nonneg_left _ (YstD_pos hb v).le
      have hv2 : v ^ 2 ≤ E := by have := sq_le_sq' hv.1 hv.2; linarith
      set s := Real.sqrt (E - v ^ 2)
      have hs : 0 ≤ s := Real.sqrt_nonneg _
      have hs2 : s ^ 2 = E - v ^ 2 := Real.sq_sqrt (by linarith)
      rw [Xst_sub_neg hb]
      have : s ≤ Real.sqrt (s ^ 2 + 2 * b) := by
        rw [show s = Real.sqrt (s ^ 2) from (Real.sqrt_sq hs).symm]
        exact Real.sqrt_le_sqrt (by rw [Real.sq_sqrt (sq_nonneg _)]; linarith)
      nlinarith
  linarith [Hst_bound hb hE]

theorem Ast_tendsto : Tendsto (Ast b) atTop atTop := by
  have h : Tendsto (fun E : ℝ => E - b * (π / 2 - 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  refine tendsto_atTop_mono' _ ?_ h
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with E hE
  exact Ast_ge hb hE

/-! ### `lem:str-area` (iv) -/

theorem Ast_Est (I : ℝ) : Ast b (Est b I) = I :=
  gAcal_Einv (Jst_contDiff hb).continuous (Jst_pos hb) (Ast_tendsto hb) I

theorem Est_nonneg {I : ℝ} (hI : 0 ≤ I) : 0 ≤ Est b I :=
  gEinv_nonneg (Jst_contDiff hb).continuous (Jst_pos hb) (Ast_tendsto hb) hI

/-- `E_st(I) ≤ I + b(π/2 - 1)` for `I ≥ 0`. -/
theorem Est_le {I : ℝ} (hI : 0 ≤ I) : Est b I ≤ I + b * (π / 2 - 1) := by
  have := Ast_ge hb (Est_nonneg hb hI); rw [Ast_Est hb] at this; linarith

end

/-! ### `prop:str-strip`: the strip map is area preserving -/

section
variable {δ : ℝ} (hδ : 0 < δ)
include hδ

theorem psiStrip_normalize :
    ContDiff ℝ ∞ (psiStrip δ) ∧
      (∀ z, LinearMap.det (fderiv ℝ (psiStrip δ) z : ℂ →ₗ[ℝ] ℂ) = 1) ∧
      (∀ z, ‖Inner.TrotInv (cf (Jst (bst δ))) 0 (Inner.Darea (cf (Jst (bst δ))) 0 z)‖ ^ 2 =
        Est (bst δ) (π * ‖z‖ ^ 2)) :=
  have hb := bst_pos hδ
  normalize_general (Jst_contDiff hb) (Jst_pos hb) (Ast_tendsto hb) (Fst_contDiff hb)
    (Fst_det hb)

/-- **`prop:str-strip`, smoothness** (in place of the paper's analyticity). -/
theorem psiStrip_smooth : ContDiff ℝ ∞ (psiStrip δ) := (psiStrip_normalize hδ).1

/-- **`prop:str-strip`.** `Ψ_strip^*(dx ∧ dT) = ω_ℂ`. -/
theorem psiStrip_symplectic (z : ℂ) : Qhat.det2 (fderiv ℝ (psiStrip δ) z) = 1 := by
  rw [Qhat.det2_eq]; exact (psiStrip_normalize hδ).2.1 z

/-- **`prop:str-strip`.** `R_st(x) + V_st(T) = E_st(π|z|²)` for `x + iT = Ψ_strip(z)`. -/
theorem psiStrip_level (z : ℂ) :
    Rst (bst δ) (psiStrip δ z).re + Vst (bst δ) (psiStrip δ z).im = Est (bst δ) (π * ‖z‖ ^ 2) := by
  rw [psiStrip, level_Fst (bst_pos hδ), (psiStrip_normalize hδ).2.2 z]

theorem psiStrip_mem (z : ℂ) :
    0 < (psiStrip δ z).re ∧ 0 < (psiStrip δ z).im ∧ (psiStrip δ z).im < 1 :=
  (Fst_bijOn (bst_pos hδ)).1 (mem_univ _)

/-- **`prop:str-strip`.** `Ψ_strip` is a bijection of `ℂ` onto the strip `(0, ∞) × (0, 1)`. -/
theorem psiStrip_bijOn :
    BijOn (psiStrip δ) univ {z : ℂ | 0 < z.re ∧ 0 < z.im ∧ z.im < 1} := by
  have hb := bst_pos hδ
  set J := Jst (bst δ)
  have hJ := Jst_contDiff hb
  have hp := Jst_pos hb
  have htop := Ast_tendsto hb
  have hDb : Function.Bijective (Inner.Darea (cf J) 0) :=
    ⟨fun a b h => by rw [← DareaInv_Darea hJ hp htop a, h, DareaInv_Darea hJ hp htop b],
      fun y => ⟨DareaInv J y, Darea_DareaInv hJ hp y⟩⟩
  have hTb : Function.Bijective (Inner.TrotInv (cf J) 0) :=
    ⟨fun a b h => by rw [← Trot_TrotInv hJ hp a, h, Trot_TrotInv hJ hp b],
      fun y => ⟨Inner.Trot (cf J) 0 y, TrotInv_Trot hJ hp y⟩⟩
  have hc : psiStrip δ = Fst (bst δ) ∘ (Inner.TrotInv (cf J) 0 ∘ Inner.Darea (cf J) 0) := rfl
  rw [hc]
  exact (Fst_bijOn hb).comp ⟨mapsTo_univ _ _, (hTb.comp hDb).injective.injOn,
    fun y _ => by
      obtain ⟨x, hx⟩ := (hTb.comp hDb).2 y; exact ⟨x, mem_univ _, hx⟩⟩

/-! ### `prop:str-strip` -/

/-- **`prop:str-strip`.** `0 < x`. -/
theorem psiStrip_x_pos (z : ℂ) : 0 < (psiStrip δ z).re := (psiStrip_mem hδ z).1

/-- **`prop:str-strip` (11).** `x < π|z|² + δ/2` (and `0 < T < 1`, `psiStrip_mem`). -/
theorem psiStrip_x_lt (z : ℂ) : (psiStrip δ z).re < π * ‖z‖ ^ 2 + δ / 2 := by
  have hb := bst_pos hδ
  have hI : 0 ≤ π * ‖z‖ ^ 2 := by positivity
  have hE := Est_le hb hI
  have hlev := psiStrip_level hδ z
  obtain ⟨hx, hT0, hT1⟩ := psiStrip_mem hδ z
  have hV := Vst_nonneg hb hT0 hT1
  have hx' := lt_of_Rst_le hb hx (show Rst (bst δ) (psiStrip δ z).re ≤ Est (bst δ) (π * ‖z‖ ^ 2)
    by linarith)
  have : bst δ * (π / 2) = δ / 2 := by unfold bst; field_simp
  nlinarith

/-! ### `prop:str-strip` -/

end

end SymplecticPacking.Strip
