import SymplecticPacking.Effective.PackingCertificatePolynomialCode
import SymplecticPacking.Effective.PackingCertificateField

/-!
# The universal polynomial field evaluator

One universal exact-rational polynomial field evaluator for every finite candidate.
-/

namespace SymplecticPacking.Effective.PackingPolynomialCode
open RationalCode PackingPolynomial
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def minCode (x y : ℕ) : ℕ := negCode (maxCode (negCode x) (negCode y))
@[irreducible] def clipCode (a b x : ℕ) : ℕ := maxCode a (minCode x b)
def natCode (a : ℕ) : ℕ := encode a 0 0

theorem value_minCode (x y : ℕ) : value (minCode x y)=min (value x) (value y) := by
  simp only [minCode,value_negCode,value_maxCode]
  by_cases h : value x≤value y
  · rw [max_eq_left (neg_le_neg h),min_eq_left h,neg_neg]
  · rw [max_eq_right (neg_le_neg (le_of_not_ge h)),min_eq_right (le_of_not_ge h),neg_neg]

theorem value_clipCode (a b x : ℕ) :
    value (clipCode a b x)=max (value a) (min (value x) (value b)) := by
  simp [clipCode, value_minCode, value_maxCode]

@[simp] theorem value_natCode (a : ℕ) : value (natCode a)=(a:ℚ) := by
  simp [natCode, value_encode]

theorem primitive_natCode : Primrec natCode :=
  Primrec₂.natPair.comp (Primrec₂.natPair.comp Primrec.id (Primrec.const 0)) (Primrec.const 0)

theorem primitive_minCode : Primrec₂ minCode :=
  primitive_negCode.comp (primitive_maxCode.comp
    (primitive_negCode.comp Primrec.fst) (primitive_negCode.comp Primrec.snd))

theorem primitive_clipCode :
    Primrec (fun a : ℕ × (ℕ × ℕ) => clipCode a.1 a.2.1 a.2.2) := by
  unfold clipCode
  exact primitive_maxCode.comp Primrec.fst (primitive_minCode.comp
    (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))

@[irreducible] def spatialClipCode (B x : ℕ) : ℕ :=
  clipCode (negCode (divideNatCode (natCode B) 1)) (divideNatCode (natCode B) 1) x

theorem primitive_spatialClipCode : Primrec₂ spatialClipCode := by
  have compose (a b c : ℕ × ℕ → ℕ) (ha : Primrec a) (hb : Primrec b) (hc : Primrec c) :
      Primrec (fun x => clipCode (a x) (b x) (c x)) := by
    exact primitive_clipCode.comp (ha.pair (hb.pair hc))
  have hb : Primrec (fun a : ℕ × ℕ => divideNatCode (natCode a.1) 1) :=
    primitive_divideNatCode.comp (primitive_natCode.comp Primrec.fst) (Primrec.const 1)
  have hn : Primrec (fun a : ℕ × ℕ => negCode (divideNatCode (natCode a.1) 1)) :=
    primitive_negCode.comp hb
  change Primrec (fun a : ℕ × ℕ => spatialClipCode a.1 a.2)
  unfold spatialClipCode
  exact compose _ _ _ hn hb Primrec.snd

def pointState (d B time state : ℕ) : ODECode.State (d+1) :=
  Fin.cons (clipCode zeroCode oneCode time) (fun j =>
    spatialClipCode B (ODECode.decodeState d state j))

def pointCode (d B time state : ℕ) : ℕ := ODECode.encodeState (d+1) (pointState d B time state)

theorem pointState_real (d B time state : ℕ) :
    ODECode.realState (pointState d B time state)=
      clippedPoint d B (value time:ℝ) (ODECode.realState (ODECode.decodeState d state)) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [ODECode.realState, pointState, clippedPoint, value_clipCode, value_zeroCode,
      oneCode, value_encode, clip, Rat.cast_max, Rat.cast_min]
  · norm_num [ODECode.realState, pointState,spatialClipCode, clippedPoint, value_clipCode, value_negCode,
      value_divideNatCode, clip, Rat.cast_max, Rat.cast_min,neg_div]

def fieldState (n : ℕ) (program : List ℕ) (B input : ℕ) : ODECode.State (2*n) :=
  fun i =>
    let point := pointCode (2*n) B (Nat.unpair input).1 (Nat.unpair (Nat.unpair input).2).1
    if h : i.val<n then derivativeEvaluate (2*n+1) (i.val+n+1) program point
    else negCode (derivativeEvaluate (2*n+1) (i.val-n+1) program point)

@[irreducible] def fieldCode (n : ℕ) (program : List ℕ) (B input : ℕ) : ℕ :=
  ODECode.encodeState (2*n) (fieldState n program B input)

theorem derivativeAtPoint (d B time state : ℕ) (program : List ℕ) (j : Fin (d+1)) :
    (value (derivativeEvaluate (d+1) j.val program (pointCode d B time state)):ℝ)=
      realEval (d+1) (derivative j.val (programExpression program))
        (clippedPoint d B (value time:ℝ) (ODECode.realState (ODECode.decodeState d state))) := by
  rw [derivativeEvaluate_value (d+1) (pointCode d B time state) j program, rationalEval_cast]
  change realEval (d+1) (derivative j.val (programExpression program))
    (ODECode.realState (ODECode.decodeState (d+1) (pointCode d B time state))) = _
  rw [pointCode, ODECode.decodeState_encodeState, pointState_real]

/-- The universal arithmetic evaluator computes the genuine clipped polynomial
Hamiltonian field, exactly at every rational query. -/
theorem fieldCode_real (n B input : ℕ) (program : List ℕ) :
    ODECode.realState (ODECode.decodeState (2*n) (fieldCode n program B input)) =
      field n B (programExpression program) (value (Nat.unpair input).1:ℝ)
        (ODECode.realState (ODECode.decodeState (2*n) (Nat.unpair (Nat.unpair input).2).1)) := by
  rw [fieldCode, ODECode.decodeState_encodeState]
  funext i
  simp only [ODECode.realState, fieldState, field]
  split_ifs with hi
  · exact derivativeAtPoint (2*n) B _ _ program ⟨i.val+n+1, by omega⟩
  · rw [value_negCode, Rat.cast_neg]
    exact congrArg Neg.neg (derivativeAtPoint (2*n) B _ _ program
      ⟨i.val-n+1, by have := i.isLt; omega⟩)

def decodeProgram (code : ℕ) : List ℕ :=
  (Encodable.decode (α := List ℕ) code).getD []

/-- The third query argument carries the finite candidate `(B,program)`.
All queries are exact, so no accuracy parameter and no solution oracle are used. -/
def universalField (n input : ℕ) : ℕ :=
  let candidate := (Nat.unpair (Nat.unpair input).2).2
  fieldCode n (decodeProgram (Nat.unpair candidate).2) (Nat.unpair candidate).1 input

theorem universalField_real (n B time state : ℕ) (program : List ℕ) :
    ODECode.realState (ODECode.decodeState (2*n)
      (universalField n (Nat.pair time (Nat.pair state (Nat.pair B (Encodable.encode program)))))) =
      field n B (programExpression program) (value time:ℝ)
        (ODECode.realState (ODECode.decodeState (2*n) state)) := by
  simpa only [universalField, Nat.unpair_pair, decodeProgram, Encodable.encodek,
    Option.getD_some] using fieldCode_real n B
      (Nat.pair time (Nat.pair state (Nat.pair B (Encodable.encode program)))) program

end SymplecticPacking.Effective.PackingPolynomialCode
