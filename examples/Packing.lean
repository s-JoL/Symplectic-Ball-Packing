import SymplecticPacking.Effective.ExecutablePacking

#print axioms NativePacking.solveRational
#print axioms NativePacking.solveName

namespace NativePacking
open SymplecticPacking SymplecticPacking.Effective
open RationalCode PackingSearch PackingCertificateCode
open Lean

def ratJson (q : ℚ) : Json :=
  Json.mkObj [("numerator",toJson q.num),("denominator",toJson q.den)]

def fixtureJson : Json :=
  let e : PackingPolynomial.Expr := .add
    (.mul (.var 0) (.mul (.var 1) (.var 3)))
    (.add (.mul (.var 2) (.var 2)) (.mul (.const (ofRat 3)) (.var 4)))
  let x : Fin 5 → ℚ := ![1/2,1,2,3,4]
  let program := PackingPolynomial.expressionProgram e
  let state := ODECode.encodeState 5 (fun i => ofRat (x i))
  let gradient := (List.range 4).map (fun i => value (PackingPolynomialCode.derivativeEvaluate 5 (i+1) program state))
  Json.mkObj [("kind",toJson "exact-polynomial-and-derivative-fixture"),
    ("program",toJson program),("box",toJson (32:ℕ)),
    ("point",toJson ((List.ofFn x).map ratJson)),
    ("value",ratJson (PackingPolynomial.rationalEval 5 e x)),
    ("gradient",toJson (gradient.map ratJson)),
    ("budget",toJson (PackingPolynomialCode.programBudget 32 program)),
    ("packing_certificate_returned",toJson false)]

def outputJson {k : ℕ} {epsilon : ℝ} (out : Output k epsilon) : Json :=
  let a := decodeCandidate out.stage
  Json.mkObj [("format", toJson "native-packing-search-output-v1"), ("k",toJson k),
    ("radius_numerator",toJson out.radius.num), ("radius_denominator",toJson out.radius.den),
    ("stage",toJson out.stage), ("box",toJson a.2.1), ("program",toJson a.2.2.2.2.2),
    ("whole_closed_ball_certificate",toJson true),
    ("coordinate_order",toJson "q1,q2,p1,p2"),
    ("hamiltonian",toJson "boxCut(B,y) * prefixPolynomial(t,y); time is not clipped")]

def dispatch (mode : String) (k : ℕ) (hk : 9 ≤ k) (q : ℚ) (h0 : 0 < q) (h1 : q < 1) : IO UInt32 := do
  let stdout ← IO.getStdout
  if mode == "fixture" then
    stdout.putStrLn fixtureJson.compress
    return 0
  else if mode == "radius" then
    let R := chooseRadius hk h0 h1
    stdout.putStrLn ((Json.mkObj [("radius_numerator",toJson (value R.val).num),
      ("radius_denominator",toJson (value R.val).den),
      ("packing_certificate_returned",toJson false)]).compress)
    return 0
  else if mode == "seed" then
    let R := chooseRadius hk h0 h1
    stdout.putStrLn ((Json.mkObj [("radius_numerator",toJson (value R.val).num),
      ("radius_denominator",toJson (value R.val).den),
      ("stage",toJson (identitySeed k)), ("passed",toJson (checkStage k R.val (identitySeed k)))]).compress)
    return 0
  else if mode == "solve" then
    stdout.putStrLn (outputJson (solveRational hk h0 h1)).compress
    return 0
  else if mode == "solve-name" then
    let name : ℕ → ℕ := fun _ => ofRat q
    have hn : CodeName.Names name (q:ℝ) := by
      simpa only [name,value_ofRat] using CodeName.constant_spec (ofRat q)
    let out := solveName hk name hn (by exact_mod_cast h0) (by exact_mod_cast h1)
    stdout.putStrLn (outputJson out).compress
    return 0
  else
    (← IO.getStderr).putStrLn "mode must be radius, seed, solve, solve-name, or fixture"
    return 2

end NativePacking

def runCommand (args : List String) : IO UInt32 := do
  match args with
  | [mode,ks,ns,ds] =>
    match ks.toNat?, ns.toInt?, ds.toNat? with
    | some k, some numerator, some denominator =>
      if denominator == 0 then
        (← IO.getStderr).putStrLn "positive denominator required"
        return 2
      let q : ℚ := (numerator:ℚ)/(denominator:ℚ)
      if hk : 9 ≤ k then
        if h0 : 0 < q then
          if h1 : q < 1 then
            NativePacking.dispatch mode k hk q h0 h1
          else
            (← IO.getStderr).putStrLn "epsilon must be below one"; return 2
        else
          (← IO.getStderr).putStrLn "epsilon must be positive"; return 2
      else
        (← IO.getStderr).putStrLn "k must be at least nine"; return 2
    | _,_,_ =>
      (← IO.getStderr).putStrLn "invalid integer arguments"; return 2
  | _ =>
    (← IO.getStderr).putStrLn "usage: MODE K EPSILON_NUMERATOR EPSILON_DENOMINATOR"
    return 2

def main (args : List String) : IO UInt32 := do
  if args == ["batch"] then
    let input ← IO.getStdin
    let output ← IO.getStdout
    let mut running := true
    while running do
      let line ← input.getLine
      if line.isEmpty then running := false
      else
        let command := (line.trimAscii.toString.splitOn " ").filter (fun x => !x.isEmpty)
        if command == ["quit"] then running := false
        else
          let result ← runCommand command
          output.flush
          if result != 0 then return result
    return 0
  else runCommand args
