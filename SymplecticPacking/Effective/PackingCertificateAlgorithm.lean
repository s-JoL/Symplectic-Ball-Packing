import SymplecticPacking.Effective.PackingCertificateOriginalInput
import SymplecticPacking.General.Main
import SymplecticPacking.General.TargetShrink

/-!
# The packing algorithm on original names

The public algorithm reads only the original capacity and centre names.
-/

noncomputable section

namespace SymplecticPacking.Effective.PackingSearch
open RationalCode PackingCertificate Problem

/-- Target capacity is index zero; source capacity `i` is index `i+1`.
Unused entries repeat the target, so no extra real input is required. -/
def capacityFamily {k : ℕ} (C : ℝ) (c : Fin k → ℝ) (i : ℕ) : ℝ :=
  if h : i≠0 ∧ i-1<k then c ⟨i-1,h.2⟩ else C

@[simp] theorem capacityFamily_zero {k : ℕ} (C : ℝ) (c : Fin k → ℝ) :
    capacityFamily C c 0=C := by simp [capacityFamily]

@[simp] theorem capacityFamily_source {k : ℕ} (C : ℝ) (c : Fin k → ℝ) (i : Fin k) :
    capacityFamily C c (i.val+1)=c i := by
  simp [capacityFamily,i.isLt]

/-- The inputs consist of the original scalar names and their accuracy proofs.
There is no geometry, flow, radius or certificate oracle in this structure. -/
structure OriginalNames (O : Set (ℕ →. ℕ)) (n k : ℕ) (C : ℝ)
    (c : Fin k → ℝ) (s : Fin k → E n) where
  capacities : Family.Evaluator O (capacityFamily C c)
  centres : ℕ → ℕ
  centre_names : ∀ i : Fin k,∀ j : Fin (2*n),Names
    (fun p=>value (centres (Nat.pair (Nat.pair i.val p) j.val))) (s i j)
  centre_recursive : Oracle.Total O centres

/-- Exactly the two original input-name streams, with no auxiliary oracle. -/
def originalOracles (capacities centres : ℕ → ℕ) : Set (ℕ →. ℕ) :=
  {fun x=>Part.some (capacities x),fun x=>Part.some (centres x)}

def OriginalNames.ofQueries {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (capacities centres : ℕ → ℕ) (hcap : Family.Names capacities (capacityFamily C c))
    (hcentre : ∀ i : Fin k,∀ j : Fin (2*n),Names
      (fun p=>value (centres (Nat.pair (Nat.pair i.val p) j.val))) (s i j)) :
    OriginalNames (originalOracles capacities centres) n k C c s where
  capacities := ⟨capacities,hcap,Oracle.query (q:=capacities) (Set.mem_insert _ _)⟩
  centres := centres
  centre_names := hcentre
  centre_recursive := Oracle.query (q:=centres) (Set.mem_insert_of_mem _ (Set.mem_singleton _))

private theorem capacityFamily_nonneg {n k : ℕ} {C : ℝ} {c : Fin k → ℝ}
    (hA : Admissible n k C c) : ∀ i,0≤capacityFamily C c i := by
  intro i
  unfold capacityFamily
  split_ifs with h
  · exact (hA.c_pos ⟨i-1,h.2⟩).le
  · exact hA.C_pos.le

theorem OriginalNames.validCapacities {O : Set (ℕ →. ℕ)} {n k : ℕ} {C : ℝ}
    {c : Fin k → ℝ} {s : Fin k → E n} (input : OriginalNames O n k C c s)
    (hA : Admissible n k C c) : ValidCapacities input.capacities.code :=
  ⟨capacityFamily C c,input.capacities.names,capacityFamily_nonneg hA⟩

theorem radius_names {O : Set (ℕ →. ℕ)} {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (input : OriginalNames O n k C c s) (hA : Admissible n k C c) :
    (∀ i : Fin k,Names
      (fun p=>value (sourceRadius (capacityRadiusCode input.capacities.code (input.validCapacities hA)) (Nat.pair i.val p)))
      (Real.sqrt (c i/Real.pi))) ∧
    Names (fun p=>value (targetRadius (capacityRadiusCode input.capacities.code (input.validCapacities hA)) p)) (Real.sqrt (C/Real.pi)) := by
  have hn:=capacityRadiusCode_names (input.validCapacities hA) input.capacities.names
    (capacityFamily_nonneg hA)
  constructor
  · intro i
    simpa only [CodeName.Names,Family.slice,sourceRadius,Nat.unpair_pair,capacityFamily_source]
      using hn (i.val+1)
  · simpa only [CodeName.Names,Family.slice,targetRadius,capacityFamily_zero]
      using hn 0

/-- Existence of the geometric packing is used solely to prove halting of the
finite search. None of its semantic construction is evaluated by the machine. -/
theorem actual_exists_stage {O : Set (ℕ →. ℕ)} {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (input : OriginalNames O n k C c s) (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) :
    ∃ st,stageFailure input.centres (sourceRadius (capacityRadiusCode input.capacities.code (input.validCapacities hA)))
      (targetRadius (capacityRadiusCode input.capacities.code (input.validCapacities hA))) n k st=0 := by
  obtain ⟨C₀,hC₀,hC₀C,hpack⟩ := (General.packing_main hA hs).exists_smaller_target hA.C_pos
  have hr:=radius_names input hA
  exact exists_stage input.centres _ _ hpack hC₀
    (show C₀<(C₀+C)/2 by linarith) (show (C₀+C)/2<C by linarith)
    hA.c_pos input.centre_names hr.1 hr.2

noncomputable def selectedStage {O : Set (ℕ →. ℕ)} {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (input : OriginalNames O n k C c s) (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) : ℕ :=
  Nat.find (actual_exists_stage input hA hs)

noncomputable def compiledHamiltonian {O : Set (ℕ →. ℕ)} {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (input : OriginalNames O n k C c s) (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) :
    ℝ → E n → ℝ := (stageOutput n (selectedStage input hA hs)).hamiltonian

theorem compiledHamiltonian_spec {O : Set (ℕ →. ℕ)} {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (input : OriginalNames O n k C c s) (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) :
    PackingSpec n k C c s (compiledHamiltonian input hA hs) := by
  have hr:=radius_names input hA
  exact stage_sound input.centres _ _ (Nat.find_spec (actual_exists_stage input hA hs))
    hA.C_pos hA.c_pos input.centre_names hr.1 hr.2

/-- The finite result of the machine is a single natural-number code. -/
noncomputable def compiledCode {O : Set (ℕ →. ℕ)} {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (input : OriginalNames O n k C c s) (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) : ℕ :=
  programCode (selectedStage input hA hs)

noncomputable def codeHamiltonian (n code : ℕ) : ℝ → E n → ℝ :=
  (PackingPolynomial.output n (Nat.unpair code).1
    (PackingPolynomial.programExpression (PackingStateList.decodeList (Nat.unpair code).2))).hamiltonian

theorem compiledHamiltonian_eq_code {O : Set (ℕ →. ℕ)} {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (input : OriginalNames O n k C c s) (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) :
    compiledHamiltonian input hA hs=codeHamiltonian n (compiledCode input hA hs) := by
  simp only [compiledHamiltonian,compiledCode,codeHamiltonian,programCode,stageOutput,
    PackingCertificate.candidateCode,Nat.unpair_pair,PackingStateList.decodeList,Encodable.encodek,Option.getD_some]

theorem original_program_machine_halts {O : Set (ℕ →. ℕ)} {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (input : OriginalNames O n k C c s) (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) :
    compiledCode input hA hs ∈ programSearch input.centres (sourceRadius (capacityRadiusCode input.capacities.code (input.validCapacities hA)))
      (targetRadius (capacityRadiusCode input.capacities.code (input.validCapacities hA))) (Nat.pair n k) :=
  programSearch_halts (actual_exists_stage input hA hs)

#check_explicit compiledCode
#check_explicit codeHamiltonian
#check_explicit compiledHamiltonian
end SymplecticPacking.Effective.PackingSearch
