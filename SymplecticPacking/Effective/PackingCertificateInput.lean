import SymplecticPacking.Effective.PackingCertificateTarget
import SymplecticPacking.Effective.NameArithmetic
import SymplecticPacking.Effective.Pi
import SymplecticPacking.Effective.Matrix

/-!
# Rational enclosures of source and target balls

Rational source over-enclosures and target under-enclosures from original real names.
-/

noncomputable section
namespace SymplecticPacking.Effective.PackingCertificate
open RationalCode
set_option maxHeartbeats 1200000

def outerRadius (d : ℕ) (q : ℕ → ℚ) (p : ℕ) : ℚ := q p+(d+2:ℕ)*radius p
def innerRadius (q : ℕ → ℚ) (p : ℕ) : ℚ := max 0 (q p-radius p)

theorem outerRadius_bounds {q : ℕ → ℚ} {r : ℝ} (hq : Names q r) (d p : ℕ) :
    r+(d+1:ℕ)*(radius p:ℝ) ≤ (outerRadius d q p:ℝ) ∧
      (outerRadius d q p:ℝ) ≤ r+(d+3:ℕ)*(radius p:ℝ) := by
  have hh := abs_le.mp (hq p)
  simp only [outerRadius, Rat.cast_add, Rat.cast_mul, Rat.cast_natCast]
  constructor <;> push_cast <;> nlinarith

theorem innerRadius_bounds {q : ℕ → ℚ} {r : ℝ} (hq : Names q r) (hr : 0≤r) (p : ℕ) :
    r-2*(radius p:ℝ) ≤ (innerRadius q p:ℝ) ∧ (innerRadius q p:ℝ) ≤ r := by
  have hh := abs_le.mp (hq p)
  simp only [innerRadius, Rat.cast_max, Rat.cast_zero, Rat.cast_sub]
  exact ⟨(by linarith [le_max_right (0:ℝ) ((q p:ℝ)-(radius p:ℝ))]),
    max_le hr (by linarith)⟩

theorem center_error {d : ℕ} {q : Fin d → ℕ → ℚ} {s : Fin d → ℝ}
    (hq : ∀ j, Names (q j) (s j)) (p : ℕ) :
    ‖s-(fun j => (q j p:ℝ))‖ ≤ (radius p:ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (by exact_mod_cast (radius_pos p).le)).mpr
  intro j
  simpa only [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm] using hq j p

/-- The rational outer source ball contains the *entire closed original ball*.
Its extra dyadic margin also pays every coordinate error of the centre name. -/
theorem outerBall_contains {d : ℕ} {q : Fin d → ℕ → ℚ} {s x : Fin d → ℝ}
    {rq : ℕ → ℚ} {r : ℝ} (hq : ∀ j, Names (q j) (s j)) (hrq : Names rq r)
    (p : ℕ) (hx : ‖l2Vector (x-s)‖ ≤ r) :
    ‖l2Vector (x-(fun j => (q j p:ℝ)))‖ < (outerRadius d rq p:ℝ) := by
  have hc := l2_norm_le_dim_mul
    (by exact_mod_cast (radius_pos p).le) (center_error hq p)
  rw [l2Vector_sub] at hx hc ⊢
  have htri := norm_sub_le_norm_sub_add_norm_sub (l2Vector x) (l2Vector s)
    (l2Vector (fun j => (q j p:ℝ)))
  have ho := (outerRadius_bounds hrq d p).1
  have hp : (0:ℝ)<radius p := by exact_mod_cast radius_pos p
  push_cast at ho
  linarith

theorem exists_near_closedBall {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s x : E) {r δ : ℝ} (hr : 0≤r) (hδ : 0≤δ) (hx : ‖x-s‖≤r+δ) :
    ∃ y : E, ‖y-s‖≤r ∧ ‖x-y‖≤δ := by
  by_cases hxr : ‖x-s‖≤r
  · exact ⟨x,hxr,by simpa using hδ⟩
  · have hnorm : 0<‖x-s‖ := by linarith [norm_nonneg (x-s)]
    let q : ℝ := r/‖x-s‖
    have hq0 : 0≤q := div_nonneg hr hnorm.le
    have hq1 : q≤1 := (div_le_one hnorm).mpr (by linarith)
    have hmul : q*‖x-s‖=r := div_mul_cancel₀ _ hnorm.ne'
    refine ⟨s+q • (x-s),?_,?_⟩
    · simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hq0,
        hmul] using (le_rfl : r≤r)
    · have heq : x-(s+q • (x-s))=(1-q) • (x-s) := by module
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hq1)]
      nlinarith

/-- A Euclidean outer-ball test supplies a nearby original source point in the
sup norm used by the numerical verifier. The point is used only in the proof. -/
theorem exists_near_source {d : ℕ} (s x : Fin d → ℝ) {r δ : ℝ}
    (hr : 0≤r) (hδ : 0≤δ) (hx : ‖l2Vector (x-s)‖≤r+δ) :
    ∃ y : Fin d → ℝ, ‖l2Vector (y-s)‖≤r ∧ ‖x-y‖≤δ := by
  rw [l2Vector_sub] at hx
  obtain ⟨y,hy,hxy⟩ := exists_near_closedBall (l2Vector s) (l2Vector x) hr hδ hx
  refine ⟨(fun j => y j),?_,?_⟩
  · have heq : l2Vector ((fun j => y j)-s)=y-l2Vector s := by
      apply PiLp.ext
      intro j
      rfl
    rw [heq]
    exact hy
  · apply (pi_norm_le_iff_of_nonneg hδ).mpr
    intro j
    have hh := (PiLp.norm_apply_le (l2Vector x-y) j).trans hxy
    simpa only [Pi.sub_apply, PiLp.sub_apply, l2Vector_apply] using hh

/-- Every non-discarded grid node lies in an explicitly shrinking neighbourhood
of the original closed source ball. This also covers nodes outside that ball. -/
theorem nonexcluded_near_source {d : ℕ} {q : Fin d → ℕ → ℚ} {s : Fin d → ℝ}
    {rq : ℕ → ℚ} {r : ℝ} (hq : ∀ j, Names (q j) (s j)) (hrq : Names rq r)
    (hr : 0<r) (p : ℕ) (a : Fin d → ℚ) {ρ : ℚ} (hρ : 0≤ρ)
    (hc : outsideCheck a (fun j => q j p) ρ (outerRadius d rq p)=false) :
    ∃ y : Fin d → ℝ, ‖l2Vector (y-s)‖≤r ∧
      ‖ODE.castVector a-y‖≤(2*d+3:ℕ)*(radius p:ℝ)+(d:ℝ)*ρ := by
  have hp : (0:ℝ)≤radius p := by exact_mod_cast (radius_pos p).le
  have hρ' : (0:ℝ)≤ρ := by exact_mod_cast hρ
  have hob := outerRadius_bounds hrq d p
  have houter : (0:ℝ)<outerRadius d rq p := by
    have hh := hob.1
    push_cast at hh
    nlinarith
  have hsq : sqNorm (a-(fun j => q j p))≤
      (outerRadius d rq p+(d:ℚ)*ρ)^2 := by
    exact le_of_not_gt (of_decide_eq_false hc)
  have hsq' : ‖l2Vector (ODE.castVector (a-(fun j => q j p)))‖^2 ≤
      ((outerRadius d rq p:ℝ)+(d:ℝ)*ρ)^2 := by
    rw [← sqNorm_cast]
    exact_mod_cast hsq
  have hnear : ‖l2Vector (ODE.castVector (a-(fun j => q j p)))‖ ≤
      (outerRadius d rq p:ℝ)+(d:ℝ)*ρ := by
    have hb : 0 ≤ (outerRadius d rq p:ℝ)+(d:ℝ)*ρ :=
      add_nonneg houter.le (mul_nonneg (Nat.cast_nonneg d) hρ')
    exact (sq_le_sq₀ (norm_nonneg _) hb).mp hsq'
  have hcenter := l2_norm_le_dim_mul hp (center_error hq p)
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (l2Vector (ODE.castVector a)) (l2Vector (fun j => (q j p:ℝ))) (l2Vector s)
  have hcast : l2Vector (ODE.castVector (a-(fun j => q j p))) =
      l2Vector (ODE.castVector a)-l2Vector (fun j => (q j p:ℝ)) := by
    ext j
    simp [l2Vector, ODE.castVector]
  rw [hcast] at hnear
  rw [l2Vector_sub, norm_sub_rev] at hcenter
  have hδ : (0:ℝ)≤(2*d+3:ℕ)*(radius p:ℝ)+(d:ℝ)*ρ := by positivity
  apply exists_near_source s (ODE.castVector a) hr.le hδ
  rw [l2Vector_sub]
  have hh := hob.2
  push_cast at hh ⊢
  nlinarith

def outerRadiusCode (d : ℕ) (q : ℕ → ℕ) (p : ℕ) : ℕ :=
  addCode (q p) (mulCode (encode (d+2) 0 0) (dyadicCode p))

def innerRadiusCode (q : ℕ → ℕ) (p : ℕ) : ℕ :=
  maxCode zeroCode (addCode (q p) (negCode (dyadicCode p)))

theorem outerRadiusCode_value (d : ℕ) (q : ℕ → ℕ) (p : ℕ) :
    value (outerRadiusCode d q p)=outerRadius d (fun p => value (q p)) p := by
  simp [outerRadiusCode, outerRadius, value_addCode, value_mulCode, value_encode, value_dyadicCode]

theorem innerRadiusCode_value (q : ℕ → ℕ) (p : ℕ) :
    value (innerRadiusCode q p)=innerRadius (fun p => value (q p)) p := by
  simp [innerRadiusCode, innerRadius, value_maxCode, value_zeroCode, value_addCode,
    value_negCode, value_dyadicCode, sub_eq_add_neg]

/-- The fixed reciprocal of pi is reduced to rational quadrature and ordinary
arithmetic. Its lower certificate is the already proved inequality `1≤pi`. -/
def inversePiEvaluator (O : Set (ℕ →. ℕ)) :
    Family.Evaluator O (fun _ : ℕ => Real.pi⁻¹) where
  code := Matrix.reciprocal Pi.family (fun _ => 0)
  names := Matrix.reciprocal_names Pi.family_names (fun _ => by
    simp only [radius, pow_zero, Rat.cast_one, abs_of_pos Real.pi_pos]
    linarith [Real.pi_gt_three])
  recursive := Matrix.reciprocal_recursive Pi.family_recursive
    (Oracle.of_computable (Computable.const 0))

/-- Capacities supplied by the original input names are converted to geometric
radii by the verified reciprocal, multiplication and square-root programs.
No additional radius-name oracle is introduced. -/
def capacityRadiusEvaluator {O : Set (ℕ →. ℕ)} {c : ℕ → ℝ}
    (Q : Family.Evaluator O c) (hc : ∀ i, 0≤c i) :
    Family.Evaluator O (fun i => Real.sqrt (c i/Real.pi)) :=
  (((Q.mul (inversePiEvaluator O)).sqrt
    (fun i => mul_nonneg (hc i) (inv_nonneg.mpr Real.pi_pos.le))).congr
      (fun i => by rw [div_eq_mul_inv]))

end SymplecticPacking.Effective.PackingCertificate
