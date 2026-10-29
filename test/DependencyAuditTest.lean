import verification.Audit.Independence

/-!
# Regression test for the dependency audit

The curve-input audit of `verification/Audit/Independence.lean` must see through a wrapper; the
construction-side roots pass there, and the converse of Corollary D there is the positive
control.
-/

open Lean Elab Command

private theorem wrappedTwoBallBound (n : ℕ) (hn : 3 ≤ n) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hp : OAI.HigherDimensionalBallPacking.HasPacking n 2 1 ![a, b]) : a + b ≤ 1 :=
  OAI.HigherDimensionalBallPacking.normalized_two_ball_bound n hn a b ha hb hp

run_cmd do
  let env ← getEnv
  match findDependency env ``wrappedTwoBallBound (isCurveInput env) with
  | none => throwError "curve-input audit missed a wrapped two-ball obstruction"
  | some _ => logInfo "curve-input regression: wrapped two-ball obstruction detected"
