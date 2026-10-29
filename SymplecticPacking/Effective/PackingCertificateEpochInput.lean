import SymplecticPacking.Effective.PackingCertificateInput
import SymplecticPacking.Effective.PackingCertificateCode
import verification.Problem

/-!
# The radius-name family of the Epoch input

One executable radius-name family, from only the original epsilon stream.
-/

noncomputable section
namespace SymplecticPacking.Effective.PackingEpoch
open RationalCode PackingCertificateCode

def originalOracles (epsilon : ℕ → ℕ) : Set (ℕ →. ℕ) := {fun p=>Part.some (epsilon p)}

/-- The parameter k remains a runtime input; this query uses its precision component. -/
def epsilonFamily (epsilon : ℕ → ℕ) (p : ℕ) : ℕ := epsilon (Nat.unpair p).2

def radius (k : ℕ) (ε : ℝ) : ℝ := Real.sqrt (Real.sqrt ((k:ℝ)/(1-ε/2)))

attribute [local irreducible] Family.add Family.neg Family.half Family.mul Family.sqrt Matrix.reciprocal

def denominatorCode (epsilon : ℕ → ℕ) : ℕ → ℕ :=
  Family.add (Family.constant (fun _=>dimCode 1)) (Family.neg (Family.half (epsilonFamily epsilon)))

def ratioCode (epsilon : ℕ → ℕ) : ℕ → ℕ :=
  Family.mul (Family.constant dimCode) (Matrix.reciprocal (denominatorCode epsilon) (fun _=>1))

attribute [local irreducible] denominatorCode ratioCode

theorem epsilonFamily_names {ε : ℝ} (epsilon : ℕ → ℕ) (he : CodeName.Names epsilon ε) :
    Family.Names (epsilonFamily epsilon) (fun _ : ℕ=>ε) := by
  intro k p
  simpa only [Family.slice,epsilonFamily,Nat.unpair_pair] using he p

theorem denominatorCode_names {ε : ℝ} (epsilon : ℕ → ℕ) (he : CodeName.Names epsilon ε) :
    Family.Names (denominatorCode epsilon) (fun _ : ℕ=>1-ε/2) := by
  have hconst : Family.Names (Family.constant (fun _ : ℕ=>dimCode 1)) (fun _ : ℕ=>(1:ℝ)) := by
    simpa only [dimCode_value,Rat.cast_natCast,Rat.cast_one,Nat.cast_one] using
      Family.constant_spec (fun _ : ℕ=>dimCode 1)
  simpa only [denominatorCode,sub_eq_add_neg] using
    Family.add_spec hconst (Family.neg_spec (Family.half_spec (epsilonFamily_names epsilon he)))

theorem ratioCode_names {ε : ℝ} (epsilon : ℕ → ℕ) (he : CodeName.Names epsilon ε)
    (h1 : ε<1) : Family.Names (ratioCode epsilon) (fun k : ℕ=>(k:ℝ)/(1-ε/2)) := by
  have hnat : Family.Names (Family.constant dimCode) (fun k : ℕ=>(k:ℝ)) := by
    simpa only [dimCode_value,Rat.cast_natCast] using Family.constant_spec dimCode
  have hi:=Matrix.reciprocal_names (denominatorCode_names epsilon he) (k:=fun _=>1) (fun _=>by
    rw [radius_cast,abs_of_pos (show 0<1-ε/2 by linarith)]
    norm_num
    linarith)
  simpa only [ratioCode,div_eq_mul_inv] using Family.mul_spec hnat hi

theorem epsilonFamily_recursive (epsilon : ℕ → ℕ) :
    Oracle.Total (originalOracles epsilon) (epsilonFamily epsilon) := by
  have hr : Oracle.Total (originalOracles epsilon) epsilon :=
    Oracle.query (q:=epsilon) (Set.mem_singleton _)
  have hh : Oracle.Total (originalOracles epsilon) (fun p=>epsilon (Nat.unpair p).2) :=
    Oracle.comp hr Oracle.right
  exact hh.of_eq (fun _=>rfl)

theorem denominatorCode_recursive (epsilon : ℕ → ℕ) :
    Oracle.Total (originalOracles epsilon) (denominatorCode epsilon) := by
  unfold denominatorCode
  exact Family.add_recursive
    (Family.constant_recursive (Oracle.of_computable (Computable.const (dimCode 1))))
    (Family.neg_recursive (Family.half_recursive (epsilonFamily_recursive epsilon)))

theorem ratioCode_recursive (epsilon : ℕ → ℕ) :
    Oracle.Total (originalOracles epsilon) (ratioCode epsilon) := by
  unfold ratioCode
  exact Family.mul_recursive
    (Family.constant_recursive (Oracle.of_computable primitive_dimCode.to_comp))
    (Matrix.reciprocal_recursive (denominatorCode_recursive epsilon)
      (Oracle.of_computable (Computable.const 1)))

/-- Validity is proof-only: the program never receives the named real as data. -/
def ValidEpsilon (epsilon : ℕ → ℕ) : Prop :=
  ∃ ε : ℝ,CodeName.Names epsilon ε ∧ ε<1

theorem validEpsilon_of_names {ε : ℝ} (epsilon : ℕ → ℕ)
    (he : CodeName.Names epsilon ε) (h1 : ε<1) : ValidEpsilon epsilon := ⟨ε,he,h1⟩

/-- `√(k/(1-ε/2))`: one oracle query at a fixed precision and an integer square root
(`Family.sqrt`). -/
def firstRootCode (epsilon : ℕ → ℕ) (_hv : ValidEpsilon epsilon) : ℕ → ℕ :=
  Family.sqrt (ratioCode epsilon)

attribute [local irreducible] firstRootCode

theorem firstRootCode_names {ε : ℝ} (epsilon : ℕ → ℕ) (hv : ValidEpsilon epsilon)
    (he : CodeName.Names epsilon ε) (h1 : ε<1) :
    Family.Names (firstRootCode epsilon hv) (fun k : ℕ=>Real.sqrt ((k:ℝ)/(1-ε/2))) := by
  unfold firstRootCode
  exact Family.sqrt_spec (ratioCode_names epsilon he h1)
    (fun k=>div_nonneg (Nat.cast_nonneg k) (by linarith))

theorem firstRootCode_recursive (epsilon : ℕ → ℕ) (hv : ValidEpsilon epsilon) :
    Oracle.Total (originalOracles epsilon) (firstRootCode epsilon hv) := by
  unfold firstRootCode
  exact Family.sqrt_recursive (ratioCode_recursive epsilon)

/-- The executable program has only a natural-number stream and erased proof
arguments. There is no real-value parameter to evaluate or supply at runtime. -/
def radiusCode (epsilon : ℕ → ℕ) (hv : ValidEpsilon epsilon) : ℕ → ℕ :=
  Family.sqrt (firstRootCode epsilon hv)

attribute [local irreducible] radiusCode

theorem radiusCode_recursive (epsilon : ℕ → ℕ) (hv : ValidEpsilon epsilon) :
    Oracle.Total (originalOracles epsilon) (radiusCode epsilon hv) := by
  unfold radiusCode
  exact Family.sqrt_recursive (firstRootCode_recursive epsilon hv)

theorem radiusCode_names {ε : ℝ} (epsilon : ℕ → ℕ) (hv : ValidEpsilon epsilon)
    (he : CodeName.Names epsilon ε) (h1 : ε<1) :
    Family.Names (radiusCode epsilon hv) (fun k : ℕ=>radius k ε) := by
  unfold radiusCode
  simpa only [radius] using Family.sqrt_spec (firstRootCode_names epsilon hv he h1)
    (fun k=>Real.sqrt_nonneg ((k:ℝ)/(1-ε/2)))

def sourceRadii (_ : ℕ) : ℕ := dimCode 1

/-- Source query layout is ((ball index, precision), coordinate). -/
def centres (x : ℕ) : ℕ :=
  if (Nat.unpair x).2=0 then dimCode (3*(Nat.unpair (Nat.unpair x).1).1) else dimCode 0

theorem primitive_centres : Primrec centres := by
  have hi : Primrec (fun x : ℕ=>(Nat.unpair (Nat.unpair x).1).1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  exact Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 0))
    (primitive_dimCode.comp (Primrec.nat_mul.comp (Primrec.const 3) hi))
    (Primrec.const (dimCode 0))

theorem sourceRadii_names (i : ℕ) : CodeName.Names
    (fun p=>sourceRadii (Nat.pair i p)) 1 := by
  simpa [sourceRadii,dimCode_value] using CodeName.constant_spec (dimCode 1)

theorem centres_names (i : ℕ) (j : Fin 4) : CodeName.Names
    (fun p=>centres (Nat.pair (Nat.pair i p) j.val)) (Problem.epochCenter i j) := by
  intro p
  have hvalue : (RationalCode.value (centres (Nat.pair (Nat.pair i p) j.val)):ℝ)=
      Problem.epochCenter i j := by
    fin_cases j <;> simp [centres,dimCode_value,Problem.epochCenter]
  change |(RationalCode.value (centres (Nat.pair (Nat.pair i p) j.val)):ℝ)-
    Problem.epochCenter i j|≤(Effective.radius p:ℝ)
  rw [hvalue,sub_self,abs_zero]
  exact_mod_cast (Effective.radius_pos p).le

#check_explicit radiusCode
#check_explicit centres
end SymplecticPacking.Effective.PackingEpoch
