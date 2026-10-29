import Mathlib
import SymplecticPacking.Explicit.Whitelist

/-!
# Explicitness standard (level L1) and its audit command

Mathlib's real numbers use `Classical.choice`, so `#print axioms` cannot distinguish an
explicit construction from one that picks an arbitrary witness of an existence statement.
We therefore use the following *auditable* standard:

* A construction term (a `def`, not a proof) may use choice only through
  - `SymplecticPacking.Explicit.the`, the definite description of a *unique* object
    (its argument is a proof of `∃! x, P x`), or
  - Mathlib definitions on the reviewed whitelist (`Explicit/Whitelist.lean`), each of which
    is a definite description (unique limit, unique derivative, inverse of a bijection,
    decidability instance, …), with the justification written next to it.
* Every other occurrence of a choice operator (`Classical.choose`, `Exists.choose`,
  `Classical.epsilon`, `Nonempty.some`, `Function.invFun`, …) in the *non-proof* part of
  the dependency closure of the construction is a violation.

`#check_explicit c` walks the non-proof dependency closure of `c` (through project,
vendored and Mathlib definitions, skipping theorems and arguments in `Prop` positions),
prints every choice site with the definition in which it occurs, and fails if a site is
neither `the` nor on the reviewed allowlist.

**Searches.** A least-element search is accepted only over a *search type* (`ℕ`, `ℤ`,
`ℚ`, `Fin n`, `Bool`, a type with a `Fintype` instance, and finite products / lists / options /
subtypes of these) and only with a *genuinely decidable* predicate: the decidability instance
(its non-proof, non-type dependency closure) must not reach `Classical.propDecidable`,
`Classical.dec*` or any choice operator. Concretely:
* `Nat.find`, `Nat.findX`, `Nat.findGreatest`, `Int.leastOfBdd`, `Int.greatestOfBdd`: every
  `Decidable` instance argument must be genuine;
* `Explicit.the` over a search type: the predicate must have a genuine `DecidablePred` instance
  (found by instance synthesis); over any other type `the` is the definite description of a
  unique object (ODE solutions, inverses, …) and is accepted as before;
* `WellFounded.min` (least element of a set): over a search type the set must have genuinely
  decidable membership; over any other type it is a violation in project code (inside Mathlib
  it is the definite minimum of a well-founded order, e.g. `sInf` of cardinals in `Module.rank`,
  covered by the reviewed whitelist entry `WellFounded.min`);
* `Finset.min'`, `Finset.max'`, `Finset.min`, `Finset.max` over a search type: the finset term
  must be classical-free (no classical `filter`).
A definition that passes one of its own parameters to such a search becomes a *derived search
operator*: the requirement is propagated to its call sites (so wrapping `Nat.find` does not hide
the instance). A declaration containing a rejected search is *tainted*, and so is every
declaration using it; the taint is absorbed only by a reviewed whitelisted Mathlib declaration
(e.g. the covering-number `sInf` on `ℕ` inside Mathlib's Haar measure, whitelist entry
`addCHaar`), never by project code. Classical decidability outside searches (e.g. `if` on real comparisons in a
formula) remains accepted.
-/

namespace SymplecticPacking.Explicit

/-- Definite description: *the* unique `x` with `P x`. This is the only sanctioned way for a
construction in this project to use choice. -/
noncomputable def the {α : Sort*} {P : α → Prop} (h : ∃! x, P x) : α :=
  Classical.choose h.exists

theorem the_spec {α : Sort*} {P : α → Prop} (h : ∃! x, P x) : P (the h) :=
  Classical.choose_spec h.exists

theorem the_eq {α : Sort*} {P : α → Prop} (h : ∃! x, P x) {y : α} (hy : P y) : the h = y :=
  h.unique (the_spec h) hy

open Lean Meta Elab Command

/-- Choice operators: occurrences of these in construction terms are audited. -/
def choiceOperators : List Name :=
  [``Classical.choice, ``Classical.choose, ``Classical.indefiniteDescription,
   ``Classical.strongIndefiniteDescription, ``Classical.epsilon, ``Exists.choose,
   ``Nonempty.some, ``Classical.arbitrary, ``Classical.ofNonempty, ``Function.invFun,
   ``Function.invFunOn, ``Function.surjInv, ``Set.Nonempty.some,
   -- not a choice operator, but an unfinished construction must not pass the audit
   ``sorryAx]

/-- Operators that are always acceptable: the unique-choice wrapper and decidability
instances (an `if` on a proposition has a definite value). The audit stops at them. -/
def acceptedOperators : List (Name × String) :=
  [(``SymplecticPacking.Explicit.the, "definite description of a unique object (∃!)"),
   (``Classical.propDecidable, "decidability instance"),
   (``Classical.dec, "decidability instance"),
   (``Classical.decEq, "decidability instance"),
   (``Classical.decPred, "decidability instance"),
   (``Classical.decRel, "decidability instance")]

/-- Is `n` declared in this project or in the vendored OAI library (or in the current file)? -/
def isProjectDecl (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none => true
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    (`SymplecticPacking).isPrefixOf m || (`OAI).isPrefixOf m || (`test).isPrefixOf m

/-- Match a reviewed declaration and its nested auxiliaries, without matching unrelated
declarations whose final name merely starts with the same letters. A trailing dot is
reserved for the generated module-local prefixes listed explicitly in the whitelist. -/
def reviewedNameMatches (reviewed candidate : String) : Bool :=
  reviewed == candidate || (reviewed ++ ".").isPrefixOf candidate ||
    (reviewed.endsWith "." && reviewed.isPrefixOf candidate)

/-- Accepted operator, or an occurrence inside a whitelisted *Mathlib* declaration. -/
def isAccepted (env : Environment) (op parent : Name) : Bool :=
  (acceptedOperators.lookup op).isSome ||
    (!isProjectDecl env parent &&
      mathlibWhitelist.any fun (pre, _, _) => reviewedNameMatches pre parent.toString)

def isSite (n : Name) : Bool :=
  choiceOperators.contains n || (acceptedOperators.lookup n).isSome

/-- Constants whose presence in a decidability instance makes it non-genuine. -/
def classicalNames : List Name :=
  choiceOperators ++
    [``Classical.propDecidable, ``Classical.dec, ``Classical.decEq, ``Classical.decPred,
     ``Classical.decRel, `Classical.typeDecidableEq, `Classical.decidableInhabited]

/-- Search operators whose `Decidable` instance arguments must be genuine. -/
def decidableSearchOps : List Name :=
  [`Nat.find, `Nat.findX, `Nat.findGreatest, `Int.leastOfBdd, `Int.greatestOfBdd]

/-- Least-element operators over a type parameter (checked by the searched type). -/
def typedSearchOps : List Name :=
  [``SymplecticPacking.Explicit.the, `WellFounded.min, `Finset.min', `Finset.max',
   `Finset.min, `Finset.max]

/-- A requirement attached to a search operator (base or derived), in terms of argument
positions. -/
inductive Req where
  /-- argument `i` must be classical-free (a genuine decidability instance, a finset, …) -/
  | genuine (i : Nat)
  /-- if argument `ty` is a search type, the predicate (or set, if `isSet`) at argument `p`
  must be genuinely decidable; otherwise accepted iff `uniqueOk` (unique description) or the
  enclosing declaration is a Mathlib one -/
  | pred (ty p : Nat) (isSet uniqueOk : Bool)
  /-- if argument `ty` is a search type, argument `s` must be classical-free -/
  | finsetArg (ty s : Nat)
  /-- the declaration contains (transitively) a rejected search; propagated to every user and
  absorbed only by a reviewed whitelisted Mathlib declaration -/
  | taint (msg : String)
  deriving Inhabited, BEq

structure AuditState where
  visited : NameSet := {}
  /-- (choice operator or reviewed site, definition in which it occurs) -/
  sites : Array (Name × Name) := #[]
  /-- search requirements of (base or derived) search operators -/
  reqs : NameMap (Array Req) := {}
  /-- memo: first classical constant reached by the closure of a constant, if any -/
  classical : NameMap (Option Name) := {}
  searchOk : Array String := #[]
  /-- rejected searches internal to a whitelisted Mathlib declaration -/
  searchAbsorbed : Array String := #[]
  /-- first declaration through which each constant was reached (for reporting paths) -/
  parentOf : NameMap Name := {}

abbrev AuditM := StateRefT AuditState MetaM

/-- Constants occurring in non-proof positions of `e`. Arguments whose parameter is a
proposition (according to `getFunInfo`) are skipped; with `skipTypes`, arguments whose
parameter is a type or a proposition-as-type (`Sort`-valued) are skipped as well. -/
partial def nonProofConsts (e : Expr) (skipTypes := false) : MetaM (Array Name) := do
  let rec go (e : Expr) (acc : Array Name) : MetaM (Array Name) := do
    match e with
    | .const n _ => return acc.push n
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      let acc ← go f acc
      let skip ← match f with
        | .const .. =>
          try
            let info ← getFunInfoNArgs f args.size
            let mut m := info.paramInfo.map (·.isProp)
            if skipTypes then
              let sorts ← forallBoundedTelescope (← inferType f) args.size fun xs _ =>
                xs.mapM fun x => do return (← whnfD (← inferType x)).isSort
              m := (Array.range (max m.size sorts.size)).map fun i =>
                m.getD i false || sorts.getD i false
            pure m
          catch _ => pure #[]
        | _ => pure #[]
      let mut acc := acc
      for i in [:args.size] do
        if skip.getD i false then continue
        acc ← go args[i]! acc
      return acc
    | .lam n t b bi => withLocalDecl n bi t fun x => go (b.instantiate1 x) acc
    | .forallE .. => return acc
    | .letE n t v b _ => do
      let acc ← if ← isProp t then pure acc else go v acc
      withLetDecl n t v fun x => go (b.instantiate1 x) acc
    | .mdata _ b => go b acc
    | .proj _ _ b => go b acc
    | _ => return acc
  go e #[]

/-- Is `t` a type over which a least-element search is acceptable? -/
partial def isSearchType (t : Expr) : MetaM Bool := do
  let t ← whnfR (← instantiateMVars t)
  let isFinite (t : Expr) : MetaM Bool := do
    try return (← synthInstance? (← mkAppM ``Fintype #[t])).isSome catch _ => return false
  if let .forallE _ d b _ := t then
    if b.hasLooseBVars then return false
    return (← isFinite d) && (← isSearchType b)
  match t.getAppFn with
  | .const n _ =>
    if [``Nat, ``Int, ``Rat, ``Fin, ``Bool, ``Unit, ``PUnit].contains n then return true
    if [``Prod, ``PProd, ``Sum, ``List, ``Option, ``Array].contains n then
      return ← t.getAppArgs.allM isSearchType
    if n == ``Subtype then return ← isSearchType t.getAppArgs[0]!
    isFinite t
  | _ => isFinite t

/-- Does `t` have a discrete factor: is it a search type, or a product, sum, subtype, option,
list or array type one of whose type arguments has a discrete factor? A definite description
over such a type could hide a least-element search in that factor. -/
partial def hasDiscreteFactor (t : Expr) : MetaM Bool := do
  let t ← whnfR (← instantiateMVars t)
  if ← isSearchType t then return true
  match t.getAppFn with
  | .const n _ =>
    if [``Prod, ``PProd, ``Sum, ``PSum, ``Option, ``List, ``Array, ``Subtype].contains n then
      t.getAppArgs.anyM fun a => do
        if (← whnfD (← inferType a)).isSort then hasDiscreteFactor a else pure false
    else return false
  | _ => return false

/-- Base requirements of a search operator, read off its signature. -/
def baseReqs (n : Name) : MetaM (Array Req) := do
  let some ci := (← getEnv).find? n | return #[]
  forallTelescope ci.type fun xs _ => do
    let names ← xs.mapM fun x => return (← x.fvarId!.getDecl).userName
    let idx (s : String) : Option Nat := names.findIdx? (·.toString == s)
    if decidableSearchOps.contains n then
      let mut r := #[]
      for i in [:xs.size] do
        let d ← xs[i]!.fvarId!.getDecl
        if d.binderInfo.isInstImplicit && (← isClass? d.type) == some ``Decidable then
          r := r.push (.genuine i)
      return r
    if n == ``SymplecticPacking.Explicit.the then
      return match idx "α", idx "P" with
        | some a, some p => #[.pred a p false true] | _, _ => #[]
    if n == `WellFounded.min then
      return match idx "α", idx "s" with
        | some a, some s => #[.pred a s true false] | _, _ => #[]
    if typedSearchOps.contains n then
      return match idx "α", idx "s" with
        | some a, some s => #[.finsetArg a s] | _, _ => #[]
    return #[]

mutual
/-- First classical constant reached by the (non-proof, non-type) closure of `n`. -/
partial def constClassical (n : Name) : AuditM (Option Name) := do
  if classicalNames.contains n then return some n
  if let some r := (← get).classical.find? n then return r
  modify fun s => { s with classical := s.classical.insert n none }
  let r ← match (← getEnv).find? n with
    | some (.defnInfo d) => exprClassical d.value
    | some (.opaqueInfo d) => exprClassical d.value
    | _ => pure none
  modify fun s => { s with classical := s.classical.insert n r }
  return r

partial def exprClassical (e : Expr) : AuditM (Option Name) := do
  for c in ← nonProofConsts e (skipTypes := true) do
    if let some w ← constClassical c then return some w
  return none
end

def recordOk (d : Name) (msg : String) : AuditM Unit := do
  unless decidableSearchOps.contains d || typedSearchOps.contains d do
    modify fun s => { s with searchOk := s.searchOk.push msg }

/-- A rejected search found in declaration `d` (with the path by which `d` was first reached),
as a taint to be propagated to the users of `d`. -/
def recordBad (d : Name) (msg : String) : AuditM (Array Req) := do
  let st ← get
  let mut path := #[d]
  let mut cur := d
  for _ in [:40] do
    match st.parentOf.find? cur with
    | some p => if p == cur then break else path := path.push p; cur := p
    | none => break
  let via := String.intercalate " <- " (path.toList.map toString)
  return #[.taint s!"{msg}\n      reached via {via}"]

/-- Check that `a` (an argument of a search operator in declaration `d`, top-level parameters
`xs`) is classical-free. Instances coming from top-level parameters of `d` are propagated as
requirements of `d`. -/
def checkGenuine (d : Name) (xs : Array Expr) (site what : String) (a : Expr) :
    AuditM (Array Req) := do
  let a ← zetaReduce (← instantiateMVars a)
  if let some w ← exprClassical a then
    return ← recordBad d s!"{site}: {what} is not genuinely decidable (reaches {w})"
  let mut out := #[]
  for fv in (collectFVars {} a).fvarIds do
    let decl ← fv.getDecl
    if (← isClass? decl.type).isNone then continue
    match xs.findIdx? (·.fvarId! == fv) with
    | some j => out := out.push (.genuine j)
    | none =>
      return ← recordBad d s!"{site}: {what} depends on the locally bound instance \
        {decl.userName}"
  if out.isEmpty then recordOk d s!"{site}: {what} genuine"
  return out

def checkReq (d : Name) (xs : Array Expr) (c : Name) (args : Array Expr) (q : Req) :
    AuditM (Array Req) := do
  let site := s!"{c}  in  {d}"
  let argIdx (a : Expr) : Option Nat :=
    if a.isFVar then xs.findIdx? (· == a) else none
  match q with
  | .taint m => return #[.taint m]
  | .genuine i =>
    let some a := args[i]? | recordBad d s!"{site}: search operator not fully applied"
    checkGenuine d xs site s!"argument {i}" a
  | .finsetArg ty s =>
    let (some T, some S) := (args[ty]?, args[s]?)
      | recordBad d s!"{site}: search operator not fully applied"
    if let (some j, some k) := (argIdx T, argIdx S) then return #[.finsetArg j k]
    if ← isSearchType T then checkGenuine d xs site s!"finset over {← ppExpr T}" S
    else return #[]
  | .pred ty p isSet uniqueOk =>
    let (some T, some P) := (args[ty]?, args[p]?)
      | recordBad d s!"{site}: search operator not fully applied"
    if let (some j, some k) := (argIdx T, argIdx P) then return #[.pred j k isSet uniqueOk]
    if ← isSearchType T then
      let pred ← if isSet then
          withLocalDeclD `x T fun x => do mkLambdaFVars #[x] (← mkAppM ``Membership.mem #[P, x])
        else pure P
      let inst ← try synthInstance? (← mkAppM ``DecidablePred #[pred]) catch _ => pure none
      match inst with
      | none =>
        recordBad d s!"{site}: search over {← ppExpr T} whose predicate has no genuine \
          Decidable instance"
      | some inst => checkGenuine d xs site s!"predicate over {← ppExpr T}" inst
    else if uniqueOk then
      -- A definite description over a type with a discrete factor (e.g. `ℕ × ℝ`) could
      -- describe the least index satisfying an undecidable predicate; project code must
      -- describe such data by a genuinely decidable search instead.
      if isProjectDecl (← getEnv) d && (← hasDiscreteFactor T) then
        recordBad d s!"{site}: definite description over {← ppExpr T}, which has a discrete \
          factor; its predicate is not checked for genuine decidability"
      else return #[]
    else if isProjectDecl (← getEnv) d then
      recordBad d s!"{site}: least-element search over {← ppExpr T}, which is not a search type"
    else
      -- Mathlib-internal minimum of a well-founded order with no decidability instance (e.g.
      -- `sInf` of cardinals in `Module.rank`): a definite object, reviewed whitelist entry
      -- `WellFounded.min`; never accepted in project code.
      recordOk d s!"{site}: Mathlib-internal well-founded minimum over {← ppExpr T} \
        (whitelist entry WellFounded.min)"
      return #[]

mutual
/-- Visit constant `n` (occurring in `parent`): audit its non-proof closure and return its
search requirements. -/
partial def visit (parent n : Name) : AuditM (Array Req) := do
  if isSite n then
    modify fun s => { s with sites := s.sites.push (n, parent) }
    return ← baseReqs n
  if let some r := (← get).reqs.find? n then return r
  if (← get).visited.contains n then return #[]
  modify fun s => { s with visited := s.visited.insert n, parentOf := s.parentOf.insert n parent }
  let value? := match (← getEnv).find? n with
    | some (.defnInfo d) => some d.value
    | some (.opaqueInfo d) => some d.value
    | _ => none
  let mut r : Array Req := #[]
  if let some v := value? then
    r ← lambdaTelescope v fun xs body => scan n xs body
  if decidableSearchOps.contains n || typedSearchOps.contains n then
    r := (← baseReqs n) ++ r.filter (· matches .taint _)
  r := r.foldl (fun acc q => if acc.contains q then acc else acc.push q) #[]
  -- a reviewed whitelisted Mathlib declaration absorbs the rejected searches in its internals
  let env ← getEnv
  if !isProjectDecl env n &&
      mathlibWhitelist.any (fun (pre, _, _) => reviewedNameMatches pre n.toString)
  then
    for q in r do
      if let .taint m := q then
        let msg := s!"{m}\n      absorbed by whitelisted Mathlib definition {n}"
        modify fun st => { st with searchAbsorbed := st.searchAbsorbed.push msg }
    r := r.filter fun q => !(q matches .taint _)
  modify fun s => { s with reqs := s.reqs.insert n r }
  return r

/-- Scan the body `e` of declaration `d` (top-level parameters `xs`). Returns the
requirements propagated to `d`'s parameters. -/
partial def scan (d : Name) (xs : Array Expr) (e : Expr) : AuditM (Array Req) := do
  match e with
  | .const c _ =>
    let r ← visit d c
    let taints := r.filter (· matches .taint _)
    if r.size == taints.size then return taints
    return taints ++ (← recordBad d s!"{c}  in  {d}: search operator used without its arguments")
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let mut out := #[]
    match f with
    | .const c _ =>
      for q in ← visit d c do
        if q matches .taint _ then out := out.push q
        else out := out ++ (← checkReq d xs c args q)
    | _ => out := out ++ (← scan d xs f)
    let skip ← match f with
      | .const .. =>
        try
          let info ← getFunInfoNArgs f args.size
          pure (info.paramInfo.map (·.isProp))
        catch _ => pure #[]
      | _ => pure #[]
    for i in [:args.size] do
      if skip.getD i false then continue
      out := out ++ (← scan d xs args[i]!)
    return out
  | .lam n t b bi => withLocalDecl n bi t fun x => scan d xs (b.instantiate1 x)
  | .forallE .. => return #[]
  | .letE n t v b _ => do
    let o ← if ← isProp t then pure #[] else scan d xs v
    withLetDecl n t v fun x => return o ++ (← scan d xs (b.instantiate1 x))
  | .mdata _ b => scan d xs b
  | .proj _ _ b => scan d xs b
  | _ => return #[]
end

/-- Run the audit of `n`; returns the report and the number of violations. -/
def runAudit (n : Name) : MetaM (MessageData × Nat) := do
  let (open_, s) ← (visit n n).run {}
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  let mut ok : Array (Name × Name) := #[]
  for (op, parent) in s.sites do
    if op != ``sorryAx && isAccepted env op parent then ok := ok.push (op, parent)
    else bad := bad.push (op, parent)
  -- A choice site needs its enclosing dependency path for a human whitelist review.
  -- This is the first observed path, not a proof that every use has the same context.
  let pathTo (parent : Name) : String := Id.run do
    let mut current := parent
    let mut path : List Name := [parent]
    for _ in [0:64] do
      if current == n then break
      match s.parentOf.find? current with
      | none => break
      | some previous =>
        if path.contains previous then break
        path := path ++ [previous]
        current := previous
    return String.intercalate " ← " (path.map toString)
  let fmt (xs : Array (Name × Name)) : String :=
    String.intercalate "\n" ((xs.toList.map fun (a, b) =>
      s!"  {a}  in  {b}\n    dependency path: {pathTo b}").eraseDups)
  let fmtS (xs : Array String) : String :=
    String.intercalate "\n" ((xs.toList.map fun a => s!"  {a}").eraseDups)
  let searchBad := open_.filterMap fun q => match q with | .taint m => some m | _ => none
  let nopen := open_.size - searchBad.size
  let nbad := bad.size + searchBad.size
  let openMsg := (if nopen == 0 then "" else
    s!"\nopen search requirements on the parameters of {n}: {nopen}") ++
    (if s.searchAbsorbed.isEmpty then "" else
    s!"\nrejected searches internal to whitelisted Mathlib definitions \
      ({s.searchAbsorbed.size}):\n{fmtS s.searchAbsorbed}")
  let msg := m!"check_explicit {n}: {s.visited.size} definitions visited\n\
    accepted sites (`the`, decidability, whitelisted Mathlib definitions) ({ok.size}):\n{fmt ok}\n\
    accepted searches (genuinely decidable over search types; Mathlib-internal \
    well-founded minima) ({s.searchOk.size}):\n\
    {fmtS s.searchOk}{openMsg}\n\
    VIOLATIONS (choice in project/vendored code, non-whitelisted Mathlib site, sorry, or \
    search with non-genuine decidability / over a non-search type) ({nbad}):\n{fmt bad}\n\
    {fmtS searchBad}"
  return (msg, nbad)

/-- `#check_explicit c` : check the construction `c` against the explicitness standard. -/
elab "#check_explicit " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let (msg, nbad) ← runAudit n
  logInfo msg
  unless nbad == 0 do
    throwError m!"check_explicit {n}: {nbad} violation(s); see the list above"

/-- First classical constant (choice operator or classical decidability instance) in the
non-proof, non-type dependency closure of `n`, with the declaration path that reaches it. -/
def firstClassical (n : Name) : MetaM (Option (Name × List Name)) := do
  let (r, s) ← (constClassical n).run {}
  let some w := r | return none
  -- Recover one path n → … → w through the memo table.
  let env ← getEnv
  let rec path : Nat → Name → List Name → MetaM (List Name)
  | 0, _, acc => return acc.reverse
  | fuel + 1, c, acc => do
    if classicalNames.contains c then return acc.reverse
    let body? := match env.find? c with
      | some (.defnInfo d) => some d.value
      | some (.opaqueInfo d) => some d.value
      | _ => none
    let some body := body? | return acc.reverse
    for c' in ← nonProofConsts body (skipTypes := true) do
      if classicalNames.contains c' then return (c' :: acc).reverse
      if let some (some _) := s.classical.find? c' then
        return ← path fuel c' (c' :: acc)
    return acc.reverse
  return some (w, ← path 64 n [n])

/-- `#check_constructive c` : the non-proof dependency closure of `c` contains no choice
operator and no classical decidability instance. Applied to an oracle machine, this says
the machine is one fixed program in its oracle arguments: it cannot branch on undecidable
properties of the real numbers those oracles name. -/
elab "#check_constructive " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  match ← firstClassical n with
  | none => logInfo m!"check_constructive {n}: no classical constant in the computational closure"
  | some (w, p) =>
    throwError m!"check_constructive {n}: reaches {w} via {String.intercalate " → " (p.map toString)}"

/-- `#check_constructive_rejects c` : regression test, succeeds iff `#check_constructive c` fails. -/
elab "#check_constructive_rejects " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  match ← firstClassical n with
  | none => throwError m!"check_constructive_rejects {n}: expected a classical constant, found none"
  | some (w, p) =>
    logInfo m!"check_constructive_rejects {n}: rejected, reaches {w} via {String.intercalate " → " (p.map toString)}"

/-- `#check_explicit_rejects c` : regression test, succeeds iff `#check_explicit c` fails. -/
elab "#check_explicit_rejects " id:ident : command => liftTermElabM do
  let n ← realizeGlobalConstNoOverloadWithInfo id
  let (msg, nbad) ← runAudit n
  logInfo msg
  if nbad == 0 then
    throwError m!"check_explicit_rejects {n}: expected a violation, but the audit passed"

end SymplecticPacking.Explicit
