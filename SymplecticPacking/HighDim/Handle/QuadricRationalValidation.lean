import SymplecticPacking.HighDim.Handle.FiniteRationalGrid

/-!
# Rational validation of ordinary grid boxes

Exact rational validation of ordinary grid boxes.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.DiagonalQuadrics

def rationalNormSq (q : ℚ × ℚ) : ℚ := q.1^2+q.2^2

def rationalSquareDifferenceNormSq (q : ℚ × ℚ) (b : ℚ) : ℚ :=
  (q.1^2-q.2^2-b)^2+(2*q.1*q.2)^2

theorem rationalNormSq_cast (q : ℚ × ℚ) :
    (rationalNormSq q : ℝ) = ‖rationalComplex q‖^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [rationalNormSq, rationalComplex]
  ring

theorem rationalSquareDifferenceNormSq_cast (q : ℚ × ℚ) (b : ℚ) :
    (rationalSquareDifferenceNormSq q b : ℝ) = ‖rationalComplex q^2-(b:ℂ)‖^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [rationalSquareDifferenceNormSq, rationalComplex,
    pow_two, Complex.mul_re, Complex.mul_im]
  ring

/-- All tests are exact rational comparisons; no equality/ordering oracle on roots is used. -/
def rationalOrdinaryValid {m : ℕ} (a : Fin m → ℚ) (R r η : ℚ) (q : ℚ × ℚ) : Prop :=
  0 < r ∧ r ≤ 1/4 ∧ 0 < η ∧
    2*r*(2*(R+1)+2*r) < η^2/2 ∧
    rationalNormSq q < (R+1/2)^2 ∧
    ∀ j, (η^2/2)^2 < rationalSquareDifferenceNormSq q (a j)

instance {m : ℕ} (a : Fin m → ℚ) (R r η : ℚ) (q : ℚ × ℚ) :
    Decidable (rationalOrdinaryValid a R r η q) := by
  unfold rationalOrdinaryValid
  infer_instance

theorem rationalOrdinaryValid_sound {m : ℕ} (a : Fin m → ℚ) {R r η : ℚ}
    (hR : 0 ≤ R) (q : ℚ × ℚ) (h : rationalOrdinaryValid a R r η q)
    (ε : Fin m → Bool) :
    let ac := fun j => (a j : ℂ)
    QuadricBoxCode.Valid ac (.ordinary q ε r) ∧
      QuadricBoxCode.Inside ac ((R:ℝ)+1) (.ordinary q ε r) := by
  rcases h with ⟨hr, hrsmall, hη, hbudget, hq, hd⟩
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  have hrsmall' : (r:ℝ) ≤ 1/4 := by
    have hh : (r:ℝ) ≤ ((1/4:ℚ):ℝ) := Rat.cast_le.mpr hrsmall
    norm_num at hh
    exact hh
  have hη' : 0 < (η:ℝ) := by exact_mod_cast hη
  have hR' : 0 ≤ (R:ℝ) := by exact_mod_cast hR
  have hq' : ‖rationalComplex q‖ < (R:ℝ)+1/2 := by
    have hh : ‖rationalComplex q‖^2 < ((R:ℝ)+1/2)^2 := by
      rw [← rationalNormSq_cast]
      have hh : (rationalNormSq q:ℝ) < (((R+1/2)^2:ℚ):ℝ) := Rat.cast_lt.mpr hq
      norm_num at hh
      exact hh
    nlinarith [norm_nonneg (rationalComplex q)]
  have hbudget' : 2*(r:ℝ)*(2*((R:ℝ)+1)+2*r) < (η:ℝ)^2/2 := by exact_mod_cast hbudget
  have hm : ordinaryBoxMargin r (ordinaryPresentationCenter (fun j => (a j:ℂ)) ε (rationalComplex q)) := by
    intro j
    have hd' : (η:ℝ)^2/2 < ‖rationalComplex q^2-(a j:ℂ)‖ := by
      have hh : ((η:ℝ)^2/2)^2 < ‖rationalComplex q^2-(a j:ℂ)‖^2 := by
        rw [← rationalSquareDifferenceNormSq_cast]
        exact_mod_cast hd j
      nlinarith [norm_nonneg (rationalComplex q^2-(a j:ℂ))]
    change 2*(r:ℝ)*(2*‖rationalComplex q‖+2*r) <
      ‖signedRoot (ε j) (rationalComplex q^2-(a j:ℂ))‖^2
    rw [norm_signedRoot_sq]
    have hb : 2*(r:ℝ)*(2*‖rationalComplex q‖+2*r) ≤
        2*(r:ℝ)*(2*((R:ℝ)+1)+2*r) := by gcongr; linarith
    exact hb.trans_lt (hbudget'.trans hd')
  exact ⟨⟨hr', hm⟩, by change ‖rationalComplex q‖+2*(r:ℝ) < (R:ℝ)+1; linarith⟩

/-- The explicit mesh estimates ensure that the useful grid point passes the exact validator. -/
theorem rationalOrdinaryValid_of_grid {m : ℕ} (a : Fin m → ℚ) {R r η : ℚ}
    (hR : 0 ≤ R) (hr : 0 < r) (hrsmall : r ≤ 1/4) (hη : 0 < η)
    (hbudget : 2*r*(2*(R+1)+2*r) < η^2/2)
    (hsmall : 4*r*(2*R+4*r) < η^2)
    (x : locus (fun j => (a j : ℂ))) (hxR : ‖x.val.1‖ ≤ R)
    (hxη : ∀ j, (η:ℝ) ≤ ‖x.val.2 j‖) (q : ℚ × ℚ)
    (hq : rationalComplex q ∈ Metric.closedBall x.val.1 ((r:ℝ)/8)) :
    rationalOrdinaryValid a R r η q := by
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  have hrsmall' : (r:ℝ) ≤ 1/4 := by
    have hh : (r:ℝ) ≤ ((1/4:ℚ):ℝ) := Rat.cast_le.mpr hrsmall
    norm_num at hh
    exact hh
  have hR' : 0 ≤ (R:ℝ) := by exact_mod_cast hR
  have hη' : 0 < (η:ℝ) := by exact_mod_cast hη
  have hsmall' : 4*(r:ℝ)*(2*(R:ℝ)+4*r) < (η:ℝ)^2 := by exact_mod_cast hsmall
  have hdist : ‖rationalComplex q-x.val.1‖ ≤ (r:ℝ)/8 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hq
  have hqn : ‖rationalComplex q‖ < (R:ℝ)+1/2 := by
    have hn : ‖rationalComplex q‖ ≤ ‖rationalComplex q-x.val.1‖+‖x.val.1‖ := by
      simpa only [sub_add_cancel] using norm_add_le (rationalComplex q-x.val.1) x.val.1
    linarith
  refine ⟨hr, hrsmall, hη, hbudget, ?_, ?_⟩
  · have hh : ‖rationalComplex q‖^2 < ((R:ℝ)+1/2)^2 := by
      nlinarith [norm_nonneg (rationalComplex q)]
    rw [← rationalNormSq_cast] at hh
    apply (Rat.cast_lt (K := ℝ)).mp
    norm_num
    exact hh
  · intro j
    have hd : ‖rationalComplex q^2-x.val.1^2‖ ≤ (r:ℝ)*(2*(R:ℝ)+4*r) := by
      apply (norm_square_difference_le hq).trans
      exact mul_le_mul (by linarith) (by linarith) (by positivity) hr'.le
    have he : (x.val.2 j)^2 = (rationalComplex q^2-(a j:ℂ))-(rationalComplex q^2-x.val.1^2) := by
      rw [mem_locus.mp x.property j]
      ring
    have hl : ‖x.val.2 j‖^2 ≤ ‖rationalComplex q^2-(a j:ℂ)‖+‖rationalComplex q^2-x.val.1^2‖ := by
      rw [← norm_pow, he]
      exact norm_sub_le _ _
    have hηsq : (η:ℝ)^2 ≤ ‖x.val.2 j‖^2 := pow_le_pow_left₀ hη'.le (hxη j) 2
    have hb : (η:ℝ)^2/2 < ‖rationalComplex q^2-(a j:ℂ)‖ := by nlinarith
    have hh : ((η:ℝ)^2/2)^2 < ‖rationalComplex q^2-(a j:ℂ)‖^2 := by
      nlinarith [norm_nonneg (rationalComplex q^2-(a j:ℂ))]
    rw [← rationalSquareDifferenceNormSq_cast] at hh
    exact_mod_cast hh

#check_explicit rationalOrdinaryValid
end SymplecticPacking.HighDim.ToricPackingStages
