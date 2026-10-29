import verification.Statement
import verification.Computability
import verification.EpochComputability

/-!
# Vendored declarations used by the main theorems

Lists, by module, the declarations of the vendored library `vendor/OAI` in the complete
dependency closure (types, values and proofs) of the main theorems, and fails if any lies in one
of the library's curve-analysis directories (`Compactness`, `Continuation`, `Degree`, `Cauchy`,
`Campanato`). The list supports the mathematical review of independence from packing existence
theorems; the supplement (section "The explicitness check") summarises it.
-/

open Lean Meta Elab Command

/-- All constants in the full (types, values, proofs) dependency closure of the given roots. -/
partial def vendoredDepClosure (env : Environment) (roots : List Name) : NameSet := Id.run do
  let env := env.setExporting false
  let mut seen : NameSet := {}
  let mut stack := roots
  while !stack.isEmpty do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if seen.contains n then continue
      seen := seen.insert n
      if let some ci := env.find? n then
        let deps := ci.type.getUsedConstants ++
          ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
        for d in deps do
          unless seen.contains d do stack := d :: stack
  return seen

elab "#vendored_usage" : command => do
  let env ← getEnv
  let roots := [``four_dim_theorem, ``four_dim_stability, ``main_theorem, ``epoch_packing, ``original_name_algorithm,
    ``epoch_name_algorithm_packing, ``equal_balls, ``unequal_cone,
    ``flow_symplectic_diffeomorphism,
    ``SymplecticPacking.General.symplectic_neighbourhood_sufficient]
  let s := vendoredDepClosure env roots
  let mut byMod : Std.HashMap Name (Array Name) := {}
  for n in s.toList do
    if let some idx := env.getModuleIdxFor? n then
      let m := env.header.moduleNames[idx.toNat]!
      if (`OAI).isPrefixOf m then
        byMod := byMod.insert m ((byMod.getD m #[]).push n)
  let mods := byMod.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString)
  let forbidden := ["Compactness", "Continuation", "Degree", "Cauchy", "Campanato"].map
    fun w => Name.mkStr `OAI.Geometry.BallPacking w
  let mut out := s!"vendored modules used: {mods.size}\n"
  let mut total := 0
  for (m, ns) in mods do
    if forbidden.any (·.isPrefixOf m) then
      throwError m!"the main theorems use the vendored curve-analysis module {m}"
    let thms := ns.filter fun n => match env.find? n with | some (.thmInfo _) => true | _ => false
    total := total + ns.size
    out := out ++ s!"{m}: {ns.size} constants ({thms.size} theorems)\n"
  out := out ++ s!"total vendored constants: {total}"
  logInfo out

#vendored_usage
