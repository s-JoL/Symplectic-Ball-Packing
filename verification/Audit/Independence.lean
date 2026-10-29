import verification.Statement
import verification.Computability
import verification.EpochComputability

/-!
# The packing theorems use no packing existence theorem

`#assert_construction_independence` checks the union of the construction theorems' complete
proof dependencies. It excludes packing existence theorems, the holomorphic-line and two-ball
obstruction proofs, and the listed curve-analysis modules. `#assert_avoids_sufficiency` checks
Corollary D separately, allowing its necessary obstructions. The positive control checks that
this converse reaches `adapted_affine_line`. The single-root commands are also
available for focused checks.
-/

open Lean Meta Elab Command

/-- Is `n` a packing existence statement of the vendored library? -/
def isExistenceDecl (allowPredicate : Bool := false) (n : Name) : Bool :=
  (`OAI).isPrefixOf n &&
    ((!allowPredicate && n.getString! == "HasPacking") ||
      (n.getString!.startsWith "hasPacking_of_inequalities") ||
      n == `OAI.HigherDimensionalBallPacking.main_theorem)

/-- First forbidden declaration in the full dependency closure, including proof bodies. -/
partial def findDependencies (env : Environment) (roots : Array Name) (forbidden : Name → Bool) :
    Option (List Name) := Id.run do
  let env := env.setExporting false
  let mut seen : NameSet := {}
  let mut parent : NameMap Name := {}
  let mut stack := roots
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    if forbidden n then
      let mut path := [n]
      let mut cur := n
      for _ in [0:200] do
        match parent.find? cur with
        | some p => path := p :: path; cur := p
        | none => break
      return some path
    let some ci := env.find? n | continue
    -- `value?` defaults to excluding theorem bodies; independence needs them.
    let refs := ci.type.getUsedConstants ++
      ((ci.value? (allowOpaque := true)).map (·.getUsedConstants)).getD #[]
    for r in refs do
      unless seen.contains r do
        parent := parent.insert r n
        stack := stack.push r
  return none

def findDependency (env : Environment) (root : Name) (forbidden : Name → Bool) :
    Option (List Name) := findDependencies env #[root] forbidden

def findExistence (env : Environment) (root : Name) (allowPredicate : Bool := false) :
    Option (List Name) := findDependency env root (isExistenceDecl allowPredicate)

/-- Curve-analysis inputs and the project's rigidity wrapper. Elementary lemmas elsewhere
in the Rigidity namespace remain available to the construction. -/
def isCurveInput (env : Environment) (n : Name) : Bool := Id.run do
  if n == `OAI.HigherDimensionalBallPacking.adapted_affine_line ||
      n == `OAI.HigherDimensionalBallPacking.normalized_two_ball_bound ||
      n == `OAI.HigherDimensionalBallPacking.HasPacking.strict_pair_bound then return true
  let some idx := env.getModuleIdxFor? n | return false
  let m := env.header.moduleNames[idx.toNat]!
  if m == `SymplecticPacking.General.Rigidity ||
      m == `OAI.Geometry.BallPacking.Rigidity.TwoBallBound then return true
  return ["Compactness", "Continuation", "Degree", "Cauchy", "Campanato"].any fun s =>
    (Name.mkStr `OAI.Geometry.BallPacking s).isPrefixOf m

elab "#assert_no_curve_input " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let env ← getEnv
  match findDependency env n (isCurveInput env) with
  | none => logInfo m!"{n}: no curve-analysis or two-ball rigidity input"
  | some p => throwError m!"{n} reaches a curve input via {p}"

/-- Positive control: the converse is expected to reach the J-holomorphic line proof. -/
elab "#assert_uses_holomorphic_line " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  match findDependency (← getEnv) n
      (· == `OAI.HigherDimensionalBallPacking.adapted_affine_line) with
  | none => throwError m!"{n}: expected a dependency on the holomorphic-line proof"
  | some _ => logInfo m!"{n}: holomorphic-line dependency detected (positive control)"

elab "#assert_avoids " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  match findExistence (← getEnv) n with
  | none => logInfo m!"{n}: no packing existence theorem in the dependency closure"
  | some p => throwError m!"{n} reaches {p.getLast!} via {p}"

/-- Like `#assert_avoids`, but the predicate `HasPacking` itself is allowed: only the
sufficiency theorems and the library's `main_theorem` are forbidden. -/
elab "#assert_avoids_sufficiency " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  match findExistence (← getEnv) n (allowPredicate := true) with
  | none => logInfo m!"{n}: no packing sufficiency theorem in the dependency closure"
  | some p => throwError m!"{n} reaches {p.getLast!} via {p}"

/-- Audit the union once: every root is checked, with shared proof dependencies visited once. -/
elab "#assert_construction_independence" : command => do
  let env ← getEnv
  let roots := #[``main_theorem, ``four_dim_theorem, ``four_dim_stability,
    ``main_time_support, ``main_support_radius, ``epoch_theorem, ``epoch_theorem_ten,
    ``flow_is_integral_curve, ``flow_symplectic_diffeomorphism, ``flow_images_disjoint,
    ``equal_balls, ``unequal_cone, ``original_name_algorithm, ``epoch_name_algorithm,
    ``epoch_name_algorithm_packing, ``epoch_packing, ``flow_neighbourhood_embedding,
    ``SymplecticPacking.General.symplectic_neighbourhood_sufficient]
  match findDependencies env roots (fun n => isExistenceDecl false n || isCurveInput env n) with
  | some p => throwError m!"construction reaches a packing-existence or curve input via {p}"
  | none => logInfo m!"construction independence: {roots.size} roots PASS; no packing existence \
      theorem, curve-analysis or two-ball rigidity input (including proof bodies)"

#assert_construction_independence
#assert_avoids_sufficiency neighbourhood_criterion
#assert_uses_holomorphic_line neighbourhood_criterion
