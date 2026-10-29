import SymplecticPacking.Effective.Family
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Digit evaluators for complex roots

Uniform digit evaluators for principal complex roots of Gaussian rational data.
-/

noncomputable section

namespace SymplecticPacking.Effective.AlgebraicComplex
open RationalCode Family Complex
open scoped ComplexConjugate

/-- Both coordinates are original natural-number rational codes. -/
def value (q r : ℕ → ℕ) (c : ℕ) : ℂ :=
  ⟨(RationalCode.value (q c) : ℝ), (RationalCode.value (r c) : ℝ)⟩

variable {O : Set (ℕ →. ℕ)}

def normEvaluator (q r : ℕ → ℕ) (hq : Oracle.Total O q) (hr : Oracle.Total O r) :
    Family.Evaluator O (fun c => ‖value q r c‖) := by
  let X := Family.Evaluator.rational q hq
  let Y := Family.Evaluator.rational r hr
  let S := (X.mul X).add (Y.mul Y)
  let N := S.sqrt (fun c => by change 0 ≤ (RationalCode.value (q c):ℝ)*(RationalCode.value (q c):ℝ) +
    (RationalCode.value (r c):ℝ)*(RationalCode.value (r c):ℝ); exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))
  exact N.congr (fun c => by simp [value, Complex.norm_def, Complex.normSq_apply, pow_two])

def rootRealEvaluator (q r : ℕ → ℕ) (hq : Oracle.Total O q) (hr : Oracle.Total O r) :
    Family.Evaluator O (fun c => (Complex.sqrt (value q r c)).re) := by
  let X := Family.Evaluator.rational q hq
  let N := normEvaluator q r hq hr
  let A := (N.add X).half
  let R := A.sqrt (fun c => by
    change 0 ≤ (‖value q r c‖+(value q r c).re)/2
    apply div_nonneg _ (by norm_num)
    linarith [Complex.abs_re_le_norm (value q r c), neg_abs_le (value q r c).re])
  exact R.congr (fun c => by rw [Complex.sqrt, Complex.cpow_inv_two_re]; rfl)

def rootImagMagnitudeEvaluator (q r : ℕ → ℕ) (hq : Oracle.Total O q) (hr : Oracle.Total O r) :
    Family.Evaluator O (fun c => Real.sqrt ((‖value q r c‖-(value q r c).re)/2)) := by
  let X := Family.Evaluator.rational q hq
  let N := normEvaluator q r hq hr
  exact ((N.add X.neg).half).sqrt (fun c => by
    change 0 ≤ (‖value q r c‖-(value q r c).re)/2
    exact div_nonneg (sub_nonneg.mpr (Complex.re_le_norm _)) (by norm_num))

/-- This sign test is on the original rational input, not on a real name. -/
def negativeImaginary (r : ℕ → ℕ) (c : ℕ) : ℕ := if Less (r c) zeroCode then 1 else 0

lemma negativeImaginary_recursive {r : ℕ → ℕ} (hr : Oracle.Total O r) :
    Oracle.Total O (negativeImaginary r) := by
  have hp : Primrec (fun u => if Less u zeroCode then 1 else 0) :=
    Primrec.ite (primitive_less.comp Primrec.id (Primrec.const zeroCode))
      (Primrec.const 1) (Primrec.const 0)
  exact (Oracle.comp (Oracle.of_computable hp.to_comp) hr).of_eq (fun _ => rfl)

def rootImagEvaluator (q r : ℕ → ℕ) (hq : Oracle.Total O q) (hr : Oracle.Total O r) :
    Family.Evaluator O (fun c => (Complex.sqrt (value q r c)).im) := by
  let B := rootImagMagnitudeEvaluator q r hq hr
  let R := Family.Evaluator.select (negativeImaginary r) (negativeImaginary_recursive hr) B B.neg
  apply R.congr
  intro c
  by_cases h : Less (r c) zeroCode
  · have hi : (value q r c).im < 0 := by
      have hh := (less_iff _ _).mp h
      rw [value_zeroCode] at hh
      change (RationalCode.value (r c):ℝ) < 0
      exact_mod_cast hh
    simp only [negativeImaginary, if_pos h, one_ne_zero, if_false]
    rw [Complex.sqrt, Complex.cpow_inv_two_im_eq_neg_sqrt hi]
  · have hi : 0 ≤ (value q r c).im := by
      have hh : (0:ℚ) ≤ RationalCode.value (r c) := by
        apply le_of_not_gt
        intro hn
        exact h ((less_iff _ _).mpr (by simpa only [value_zeroCode] using hn))
      change 0 ≤ (RationalCode.value (r c):ℝ)
      exact_mod_cast hh
    simp only [negativeImaginary, if_neg h, if_true]
    rw [Complex.sqrt, Complex.cpow_inv_two_im_eq_sqrt hi]

/-- A complex-valued family with uniform rational digit evaluators for both coordinates. -/
structure Evaluator (O : Set (ℕ →. ℕ)) (z : ℕ → ℂ) where
  re : Family.Evaluator O (fun c => (z c).re)
  im : Family.Evaluator O (fun c => (z c).im)

namespace Evaluator
variable {z w : ℕ → ℂ}

def congr (Z : Evaluator O z) (h : ∀ c, z c = w c) : Evaluator O w :=
  ⟨Z.re.congr (fun c => congrArg Complex.re (h c)),
    Z.im.congr (fun c => congrArg Complex.im (h c))⟩

def neg (Z : Evaluator O z) : Evaluator O (fun c => -z c) := ⟨Z.re.neg, Z.im.neg⟩

def mul (Z : Evaluator O z) (W : Evaluator O w) : Evaluator O (fun c => z c*w c) :=
  ⟨(Z.re.mul W.re).add (Z.im.mul W.im).neg,
    (Z.re.mul W.im).add (Z.im.mul W.re)⟩

def conjugate (Z : Evaluator O z) : Evaluator O (fun c => conj (z c)) :=
  ⟨Z.re, Z.im.neg⟩

def norm (Z : Evaluator O z) : Family.Evaluator O (fun c => ‖z c‖) := by
  let S := (Z.re.mul Z.re).add (Z.im.mul Z.im)
  exact (S.sqrt (fun c => add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))).congr
    (fun c => by simp [Complex.norm_def, Complex.normSq_apply, pow_two])

/-- Coordinate distance for the product norm on the real chart plane. -/
def planeDistance (Z : Evaluator O z) (W : Evaluator O w) :
    Family.Evaluator O (fun c => dist ((z c).re, (z c).im) ((w c).re, (w c).im)) :=
  ((Z.re.add W.re.neg).absolute.maximum (Z.im.add W.im.neg).absolute).congr
    (fun c => by simp [Prod.dist_eq, Real.dist_eq, sub_eq_add_neg])

end Evaluator

/-- Gaussian rational input is represented by two finite natural codes. Every operation
below uses the native code arithmetic, including the reciprocal at zero. -/
structure GaussianFamily (O : Set (ℕ →. ℕ)) where
  realCode : ℕ → ℕ
  imagCode : ℕ → ℕ
  realRecursive : Oracle.Total O realCode
  imagRecursive : Oracle.Total O imagCode

namespace GaussianFamily

def eval (Q : GaussianFamily O) : ℕ → ℂ := value Q.realCode Q.imagCode

def evaluator (Q : GaussianFamily O) : Evaluator O Q.eval :=
  ⟨Family.Evaluator.rational Q.realCode Q.realRecursive,
    Family.Evaluator.rational Q.imagCode Q.imagRecursive⟩

private lemma total_unary {q : ℕ → ℕ} (hq : Oracle.Total O q) {f : ℕ → ℕ}
    (hf : Primrec f) : Oracle.Total O (fun c => f (q c)) :=
  Oracle.comp (Oracle.of_computable hf.to_comp) hq

private lemma total_binary {q r : ℕ → ℕ} (hq : Oracle.Total O q) (hr : Oracle.Total O r)
    {f : ℕ → ℕ → ℕ} (hf : Primrec₂ f) : Oracle.Total O (fun c => f (q c) (r c)) :=
  (Oracle.comp (Oracle.of_computable (hf.comp (Primrec.fst.comp Primrec.unpair)
    (Primrec.snd.comp Primrec.unpair)).to_comp) (Oracle.pair hq hr)).of_eq
    (fun c => by simp only [Nat.unpair_pair])

def constant (x y : ℚ) : GaussianFamily O :=
  ⟨fun _ => ofRat x, fun _ => ofRat y,
    Oracle.of_computable (Computable.const _), Oracle.of_computable (Computable.const _)⟩

lemma constant_at (x y : ℚ) (c : ℕ) :
    (constant (O := O) x y).eval c = ⟨(x:ℝ), (y:ℝ)⟩ := by
  simp [eval, constant, value, value_ofRat]

def add (Q R : GaussianFamily O) : GaussianFamily O :=
  ⟨fun c => addCode (Q.realCode c) (R.realCode c),
    fun c => addCode (Q.imagCode c) (R.imagCode c),
    total_binary Q.realRecursive R.realRecursive primitive_addCode,
    total_binary Q.imagRecursive R.imagRecursive primitive_addCode⟩

lemma add_at (Q R : GaussianFamily O) (c : ℕ) : (Q.add R).eval c = Q.eval c + R.eval c := by
  apply Complex.ext <;> simp [eval, add, value, value_addCode]

def neg (Q : GaussianFamily O) : GaussianFamily O :=
  ⟨fun c => negCode (Q.realCode c), fun c => negCode (Q.imagCode c),
    total_unary Q.realRecursive primitive_negCode, total_unary Q.imagRecursive primitive_negCode⟩

lemma neg_at (Q : GaussianFamily O) (c : ℕ) : Q.neg.eval c = -Q.eval c := by
  apply Complex.ext <;> simp [eval, neg, value, value_negCode]

def mul (Q R : GaussianFamily O) : GaussianFamily O :=
  ⟨fun c => addCode (mulCode (Q.realCode c) (R.realCode c))
      (negCode (mulCode (Q.imagCode c) (R.imagCode c))),
    fun c => addCode (mulCode (Q.realCode c) (R.imagCode c))
      (mulCode (Q.imagCode c) (R.realCode c)),
    total_binary (total_binary Q.realRecursive R.realRecursive primitive_mulCode)
      (total_unary (total_binary Q.imagRecursive R.imagRecursive primitive_mulCode) primitive_negCode)
      primitive_addCode,
    total_binary (total_binary Q.realRecursive R.imagRecursive primitive_mulCode)
      (total_binary Q.imagRecursive R.realRecursive primitive_mulCode) primitive_addCode⟩

lemma mul_at (Q R : GaussianFamily O) (c : ℕ) : (Q.mul R).eval c = Q.eval c * R.eval c := by
  apply Complex.ext <;> simp [eval, mul, value, value_addCode, value_mulCode, value_negCode,
    Complex.mul_re, Complex.mul_im, sub_eq_add_neg]

def inverse (Q : GaussianFamily O) : GaussianFamily O := by
  let d := fun c => invCode (addCode (mulCode (Q.realCode c) (Q.realCode c))
    (mulCode (Q.imagCode c) (Q.imagCode c)))
  have hd : Oracle.Total O d := total_unary
    (total_binary (total_binary Q.realRecursive Q.realRecursive primitive_mulCode)
      (total_binary Q.imagRecursive Q.imagRecursive primitive_mulCode) primitive_addCode) primitive_invCode
  exact ⟨fun c => mulCode (Q.realCode c) (d c),
    fun c => negCode (mulCode (Q.imagCode c) (d c)),
    total_binary Q.realRecursive hd primitive_mulCode,
    total_unary (total_binary Q.imagRecursive hd primitive_mulCode) primitive_negCode⟩

lemma inverse_at (Q : GaussianFamily O) (c : ℕ) : Q.inverse.eval c = (Q.eval c)⁻¹ := by
  apply Complex.ext <;> simp [eval, inverse, value, value_mulCode, value_addCode, value_negCode,
    value_invCode, Complex.inv_re, Complex.inv_im, Complex.normSq_apply, div_eq_mul_inv]

def root (Q : GaussianFamily O) : Evaluator O (fun c => Complex.sqrt (Q.eval c)) :=
  ⟨rootRealEvaluator Q.realCode Q.imagCode Q.realRecursive Q.imagRecursive,
    rootImagEvaluator Q.realCode Q.imagCode Q.realRecursive Q.imagRecursive⟩

end GaussianFamily

#check_explicit rootRealEvaluator
#check_explicit rootImagEvaluator
#check_explicit GaussianFamily.inverse
end SymplecticPacking.Effective.AlgebraicComplex
