import SymplecticPacking.Effective.NameArithmetic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# Polynomial expressions of a packing certificate

Finite rational arithmetic expressions for the polynomial part of a packing certificate.
-/

namespace SymplecticPacking.Effective.PackingPolynomial
open RationalCode
open scoped ContDiff
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Constants use the concrete natural rational codes. Out-of-range variables
denote zero, so every finite code denotes a well-defined polynomial. -/
inductive Expr where
  | const : ℕ → Expr
  | var : ℕ → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  deriving Inhabited

def eval {R : Type*} [CommRing R] (constant : ℕ → R) (x : ℕ → R) : Expr → R
  | .const c => constant c
  | .var i => x i
  | .add p q => eval constant x p+eval constant x q
  | .mul p q => eval constant x p*eval constant x q

def coordinates {R : Type*} [Zero R] {d : ℕ} (x : Fin d → R) (i : ℕ) : R :=
  if h : i<d then x ⟨i,h⟩ else 0

def realEval (d : ℕ) (e : Expr) (x : Fin d → ℝ) : ℝ :=
  eval (fun c => (value c:ℝ)) (coordinates x) e

def rationalEval (d : ℕ) (e : Expr) (x : Fin d → ℚ) : ℚ :=
  eval value (coordinates x) e

noncomputable def toPolynomial (d : ℕ) (e : Expr) : MvPolynomial (Fin d) ℚ :=
  eval (fun c => MvPolynomial.C (value c))
    (fun i => if h : i<d then MvPolynomial.X ⟨i,h⟩ else 0) e

theorem eval_toPolynomial (d : ℕ) (e : Expr) (x : Fin d → ℝ) :
    MvPolynomial.eval₂ (algebraMap ℚ ℝ) x (toPolynomial d e) = realEval d e x := by
  induction e with
  | const c => simp [toPolynomial, realEval, eval]
  | var i => simp only [toPolynomial, realEval, eval, coordinates]; split_ifs <;> simp
  | add p q hp hq =>
      simp only [toPolynomial, realEval, eval] at *
      rw [MvPolynomial.eval₂_add, hp, hq]
  | mul p q hp hq =>
      simp only [toPolynomial, realEval, eval] at *
      rw [MvPolynomial.eval₂_mul, hp, hq]

/-- Surjectivity is needed only in the nonemptiness proof. The executable search
enumerates expressions; it does not choose a representation of a supplied polynomial. -/
theorem toPolynomial_surjective (d : ℕ) : Function.Surjective (toPolynomial d) := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C q => exact ⟨.const (ofRat q), by simp [toPolynomial, eval, value_ofRat]⟩
  | add P Q hp hq =>
      obtain ⟨p, rfl⟩ := hp
      obtain ⟨q, rfl⟩ := hq
      exact ⟨.add p q, rfl⟩
  | mul_X P j hp =>
      obtain ⟨p, rfl⟩ := hp
      exact ⟨.mul p (.var j.val), by simp [toPolynomial, eval, j.isLt]⟩

theorem rationalEval_cast (d : ℕ) (e : Expr) (x : Fin d → ℚ) :
    (rationalEval d e x:ℝ) = realEval d e (fun j => (x j:ℝ)) := by
  induction e with
  | const c => rfl
  | var i => simp only [rationalEval, realEval, eval, coordinates]; split_ifs <;> simp
  | add p q hp hq => simpa only [rationalEval, realEval, eval, Rat.cast_add] using congrArg₂ (·+·) hp hq
  | mul p q hp hq => simpa only [rationalEval, realEval, eval, Rat.cast_mul] using congrArg₂ (·*·) hp hq

/-- A literal zero expression; its decoding does not search for a rational code. -/
def zero : Expr := .const zeroCode
def one : Expr := .const (encode 1 0 0)

/-- Symbolic differentiation, performed only on finite arithmetic data. -/
def derivative (j : ℕ) : Expr → Expr
  | .const _ => zero
  | .var i => if i=j then one else zero
  | .add p q => .add (derivative j p) (derivative j q)
  | .mul p q => .add (.mul (derivative j p) q) (.mul p (derivative j q))

theorem smooth (d : ℕ) (e : Expr) : ContDiff ℝ ∞ (realEval d e) := by
  induction e with
  | const c => exact contDiff_const
  | var i =>
      by_cases h : i<d
      · change ContDiff ℝ ∞ (fun x : Fin d → ℝ => coordinates x i)
        simp only [coordinates, dif_pos h]
        exact contDiff_apply (𝕜 := ℝ) (E := ℝ) (⟨i,h⟩:Fin d)
      · change ContDiff ℝ ∞ (fun x : Fin d → ℝ => coordinates x i)
        simp only [coordinates, dif_neg h]
        exact contDiff_const
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq => exact hp.mul hq

theorem derivative_update (d : ℕ) (e : Expr) (x : Fin d → ℝ) (j : Fin d) :
    HasDerivAt (fun t => realEval d e (Function.update x j t))
      (realEval d (derivative j.val e) x) (x j) := by
  induction e with
  | const c =>
      simpa only [realEval, eval, derivative, zero, value_zeroCode, Rat.cast_zero] using
        (hasDerivAt_const (x j) (value c:ℝ))
  | var i =>
      by_cases h : i<d
      · by_cases hij : i=j.val
        · have heq : (⟨i,h⟩:Fin d)=j := Fin.ext hij
          simpa only [realEval, eval, coordinates, dif_pos h, heq, Function.update_self,
            derivative, if_pos hij, one, value_encode, Nat.cast_one, Nat.cast_zero,
            sub_zero, zero_add, div_one, Rat.cast_one] using hasDerivAt_id' (x j)
        · have hne : (⟨i,h⟩:Fin d)≠j := fun e => hij (congrArg Fin.val e)
          simpa only [realEval, eval, coordinates, dif_pos h, Function.update_of_ne hne,
            derivative, if_neg hij, zero, value_zeroCode, Rat.cast_zero] using
              (hasDerivAt_const (x j) (x ⟨i,h⟩))
      · have hij : i≠j.val := fun heq => h (heq ▸ j.isLt)
        simpa only [realEval, eval, coordinates, dif_neg h, derivative, if_neg hij,
          zero, value_zeroCode, Rat.cast_zero] using hasDerivAt_const (x j) (0:ℝ)
  | add p q hp hq => exact hp.add hq
  | mul p q hp hq =>
      convert hp.mul hq using 1 <;>
        simp only [realEval, eval, derivative, Function.update_eq_self, Pi.mul_apply]
      rfl

/-- The symbolic derivative is the genuine Fréchet partial derivative, with no
derivative-value oracle or numerical finite differences. -/
theorem derivative_correct (d : ℕ) (e : Expr) (x : Fin d → ℝ) (j : Fin d) :
    fderiv ℝ (realEval d e) x (Pi.single j 1) = realEval d (derivative j.val e) x := by
  have hf := ((smooth d e).differentiable (by simp) (Function.update x j (x j))).hasFDerivAt.comp_hasDerivAt
    (x j) (hasDerivAt_update x j (x j))
  simpa only [Function.update_eq_self] using hf.unique (derivative_update d e x j)

/-- Every constant bound is a natural number computable from its original code. -/
def constantBound (c : ℕ) : ℕ := positiveNumerator c+negativeNumerator c+1

theorem constantBound_spec (c : ℕ) : |(value c:ℝ)| ≤ (constantBound c:ℝ) := by
  have hm := CodeName.value_abs_bound c
  dsimp only [constantBound]
  push_cast
  linarith

def bound (R : ℕ) : Expr → ℕ
  | .const c => constantBound c
  | .var _ => R
  | .add p q => bound R p+bound R q
  | .mul p q => bound R p*bound R q

def lip (R : ℕ) : Expr → ℕ
  | .const _ => 0
  | .var _ => 1
  | .add p q => lip R p+lip R q
  | .mul p q => bound R p*lip R q+bound R q*lip R p

/-- One coarse integer controls value, first derivatives and Lipschitz constants
of the first derivatives. It is computed by the same finite arithmetic program. -/
def budget (R : ℕ) : Expr → ℕ
  | .const c => constantBound c+1
  | .var _ => R+2
  | .add p q => budget R p+budget R q
  | .mul p q => 4*budget R p*budget R q

theorem budget_pos (R : ℕ) (e : Expr) : 0 < budget R e := by
  induction e with
  | const c => simp [budget]
  | var i => simp [budget]
  | add p q hp hq => simp only [budget]; omega
  | mul p q hp hq => simp only [budget]; positivity

theorem budget_bounds (R : ℕ) (e : Expr) :
    bound R e ≤ budget R e ∧ lip R e ≤ budget R e ∧
      ∀ j, bound R (derivative j e) ≤ budget R e ∧
        lip R (derivative j e) ≤ budget R e := by
  induction e with
  | const c => simp [budget, bound, lip, derivative, zero, constantBound, zeroCode,
      positiveNumerator, negativeNumerator, encode]
  | var i =>
      simp only [budget, bound, lip, derivative]
      refine ⟨by omega, by omega, fun j => ?_⟩
      split_ifs <;> simp [bound, lip, zero, one, constantBound, zeroCode,
        positiveNumerator, negativeNumerator, encode]
  | add p q hp hq =>
      simp only [budget, bound, lip, derivative]
      exact ⟨Nat.add_le_add hp.1 hq.1, Nat.add_le_add hp.2.1 hq.2.1,
        fun j => ⟨Nat.add_le_add (hp.2.2 j).1 (hq.2.2 j).1,
          Nat.add_le_add (hp.2.2 j).2 (hq.2.2 j).2⟩⟩
  | mul p q hp hq =>
      have hbp := budget_pos R p
      have hbq := budget_pos R q
      simp only [budget, bound, lip, derivative]
      refine ⟨?_, ?_, fun j => ⟨?_, ?_⟩⟩
      · have hh := Nat.mul_le_mul hp.1 hq.1
        nlinarith
      · have h1 := Nat.mul_le_mul hp.1 hq.2.1
        have h2 := Nat.mul_le_mul hq.1 hp.2.1
        nlinarith
      · have h1 := Nat.mul_le_mul (hp.2.2 j).1 hq.1
        have h2 := Nat.mul_le_mul hp.1 (hq.2.2 j).1
        nlinarith
      · have h1 := Nat.mul_le_mul (hp.2.2 j).1 hq.2.1
        have h2 := Nat.mul_le_mul hq.1 (hp.2.2 j).2
        have h3 := Nat.mul_le_mul hp.1 (hq.2.2 j).2
        have h4 := Nat.mul_le_mul (hq.2.2 j).1 hp.2.1
        nlinarith

theorem eval_bound (d R : ℕ) (e : Expr) {x : Fin d → ℝ}
    (hx : ∀ j, |x j| ≤ (R:ℝ)) : |realEval d e x| ≤ (bound R e:ℝ) := by
  induction e with
  | const c => exact constantBound_spec c
  | var i =>
      by_cases h : i<d
      · simpa only [realEval, eval, coordinates, dif_pos h, bound] using hx ⟨i,h⟩
      · simp [realEval, eval, coordinates, h, bound]
  | add p q hp hq =>
      change |realEval d p x+realEval d q x| ≤ ((bound R p+bound R q:ℕ):ℝ)
      push_cast
      exact (abs_add_le _ _).trans (add_le_add hp hq)
  | mul p q hp hq =>
      change |realEval d p x*realEval d q x| ≤ ((bound R p*bound R q:ℕ):ℝ)
      rw [abs_mul, Nat.cast_mul]
      exact mul_le_mul hp hq (abs_nonneg _) (Nat.cast_nonneg _)

theorem eval_lipschitz (d R : ℕ) (e : Expr) {x y : Fin d → ℝ}
    (hx : ∀ j, |x j| ≤ (R:ℝ)) (hy : ∀ j, |y j| ≤ (R:ℝ)) :
    |realEval d e x-realEval d e y| ≤ (lip R e:ℝ)*‖x-y‖ := by
  induction e with
  | const c => simp [realEval, eval, lip]
  | var i =>
      by_cases h : i<d
      · simpa only [realEval, eval, coordinates, dif_pos h, lip, Nat.cast_one, one_mul,
          Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (x-y) ⟨i,h⟩
      · simp [realEval, eval, coordinates, h, lip]
  | add p q hp hq =>
      change |(realEval d p x+realEval d q x)-(realEval d p y+realEval d q y)| ≤ _
      rw [show (realEval d p x+realEval d q x)-(realEval d p y+realEval d q y) =
        (realEval d p x-realEval d p y)+(realEval d q x-realEval d q y) by ring]
      exact (abs_add_le _ _).trans (by simpa [lip, add_mul] using add_le_add hp hq)
  | mul p q hp hq =>
      change |realEval d p x*realEval d q x-realEval d p y*realEval d q y| ≤ _
      rw [show realEval d p x*realEval d q x-realEval d p y*realEval d q y =
        realEval d p x*(realEval d q x-realEval d q y)+
          realEval d q y*(realEval d p x-realEval d p y) by ring]
      have h1 := mul_le_mul (eval_bound d R p hx) hq (abs_nonneg _)
        (Nat.cast_nonneg (bound R p))
      have h2 := mul_le_mul (eval_bound d R q hy) hp (abs_nonneg _)
        (Nat.cast_nonneg (bound R q))
      exact (abs_add_le _ _).trans (by
        simpa only [Real.norm_eq_abs, abs_mul, lip, Nat.cast_add, Nat.cast_mul,
          add_mul, mul_assoc] using add_le_add h1 h2)

/-- Prefix arithmetic programs execute the tail first. Stack underflow gives
zero, and any opcode beyond the first three is multiplication. -/
def expressionStep (cmd : ℕ) (stack : List Expr) : List Expr :=
  let tag := (Nat.unpair cmd).1
  let payload := (Nat.unpair cmd).2
  if tag=0 then .const payload :: stack
  else if tag=1 then .var payload :: stack
  else if tag=2 then .add (stack.getD 0 zero) (stack.getD 1 zero) :: stack.drop 2
  else .mul (stack.getD 0 zero) (stack.getD 1 zero) :: stack.drop 2

def expressionStack : List ℕ → List Expr
  | [] => []
  | cmd :: program => expressionStep cmd (expressionStack program)

def programExpression (program : List ℕ) : Expr := (expressionStack program).getD 0 zero

def expressionProgram : Expr → List ℕ
  | .const c => [Nat.pair 0 c]
  | .var i => [Nat.pair 1 i]
  | .add p q => Nat.pair 2 0 :: (expressionProgram p ++ expressionProgram q)
  | .mul p q => Nat.pair 3 0 :: (expressionProgram p ++ expressionProgram q)

theorem expressionProgram_stack (e : Expr) (tail : List ℕ) :
    expressionStack (expressionProgram e ++ tail) = e :: expressionStack tail := by
  induction e generalizing tail with
  | const c => simp [expressionProgram, expressionStack, expressionStep]
  | var i => simp [expressionProgram, expressionStack, expressionStep]
  | add p q hp hq =>
      simp only [expressionProgram, List.cons_append, List.append_assoc, expressionStack,
        hp, hq, expressionStep, Nat.unpair_pair]
      simp
  | mul p q hp hq =>
      simp only [expressionProgram, List.cons_append, List.append_assoc, expressionStack,
        hp, hq, expressionStep, Nat.unpair_pair]
      simp

theorem programExpression_expressionProgram (e : Expr) :
    programExpression (expressionProgram e) = e := by
  have h := expressionProgram_stack e []
  simpa only [List.append_nil, programExpression, expressionStack, List.getD_cons_zero] using
    congrArg (fun xs => xs.getD 0 zero) h

end SymplecticPacking.Effective.PackingPolynomial
