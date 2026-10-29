import verification.AxiomCheck

/-!
# Regression test for `#assert_publication_axioms`

The gate accepts a proof that uses no axiom and rejects `sorryAx`.
-/

/-- info: publication_axioms True.intro: PASS; dependencies: [] -/
#guard_msgs in
#assert_publication_axioms True.intro

/-- error: sorryAx: forbidden axiom dependencies: [sorryAx] -/
#guard_msgs in
#assert_publication_axioms sorryAx
