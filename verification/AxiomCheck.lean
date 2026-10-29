import Mathlib.Util.AssertNoSorry

/-!
# Failing kernel-dependency check for the publication

Unlike `#print axioms`, this command fails on an unapproved axiom, including a `sorryAx`
introduced in any transitive proof dependency.
-/

open Lean Elab Command

elab "#assert_publication_axioms " id:ident : command => do
  let name ← liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
  let axioms ← Lean.collectAxioms name
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let forbidden := axioms.filter fun ax => !allowed.contains ax
  unless forbidden.isEmpty do
    throwError "{name}: forbidden axiom dependencies: {forbidden}"
  logInfo m!"publication_axioms {name}: PASS; dependencies: {axioms}"
