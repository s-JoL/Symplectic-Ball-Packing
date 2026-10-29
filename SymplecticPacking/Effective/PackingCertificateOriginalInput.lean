import SymplecticPacking.Effective.PackingCertificateInput
import SymplecticPacking.Effective.PackingCertificateSearchRecursive

/-!
# Input conversion from the original name streams

Executable input conversion: the only data are the two original name streams.
-/

namespace SymplecticPacking.Effective.PackingSearch
open RationalCode PackingCertificate

attribute [local irreducible] Family.mul Family.sqrt Matrix.reciprocal

/-- A validity proof is erased; no named real is an argument of the program. -/
def ValidCapacities (q : ℕ → ℕ) : Prop :=
  ∃ c : ℕ → ℝ,Family.Names q c ∧ ∀ i,0≤c i

def inversePiCode : ℕ → ℕ := Matrix.reciprocal Pi.family (fun _=>0)

theorem inversePiCode_names : Family.Names inversePiCode (fun _ : ℕ=>Real.pi⁻¹) :=
  Matrix.reciprocal_names Pi.family_names (fun _=>by
    simp only [radius,pow_zero,Rat.cast_one,abs_of_pos Real.pi_pos]
    linarith [Real.pi_gt_three])

theorem inversePiCode_recursive {O : Set (ℕ →. ℕ)} : Oracle.Total O inversePiCode :=
  Matrix.reciprocal_recursive Pi.family_recursive (Oracle.of_computable (Computable.const 0))

def capacityQuotientCode (q : ℕ → ℕ) : ℕ → ℕ := Family.mul q inversePiCode

theorem capacityQuotientCode_names {q : ℕ → ℕ} {c : ℕ → ℝ} (hq : Family.Names q c) :
    Family.Names (capacityQuotientCode q) (fun i=>c i/Real.pi) := by
  simpa only [capacityQuotientCode,div_eq_mul_inv] using Family.mul_spec hq inversePiCode_names

def capacityRadiusCode (q : ℕ → ℕ) (_hv : ValidCapacities q) : ℕ → ℕ :=
  Family.sqrt (capacityQuotientCode q)

theorem capacityRadiusCode_names {q : ℕ → ℕ} (hv : ValidCapacities q)
    {c : ℕ → ℝ} (hq : Family.Names q c) (hc : ∀ i,0≤c i) :
    Family.Names (capacityRadiusCode q hv) (fun i=>Real.sqrt (c i/Real.pi)) := by
  unfold capacityRadiusCode
  exact Family.sqrt_spec (capacityQuotientCode_names hq) (fun i=>div_nonneg (hc i) Real.pi_pos.le)

theorem capacityRadiusCode_recursive {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ}
    (hv : ValidCapacities q) (hq : Oracle.Total O q) :
    Oracle.Total O (capacityRadiusCode q hv) := by
  unfold capacityRadiusCode
  exact Family.sqrt_recursive (Family.mul_recursive hq inversePiCode_recursive)

/-- This relabelling is independent of the dimension and the number of balls. -/
def sourceRadius (q : ℕ → ℕ) (x : ℕ) := q (Nat.pair ((Nat.unpair x).1+1) (Nat.unpair x).2)
def targetRadius (q : ℕ → ℕ) (p : ℕ) := q (Nat.pair 0 p)

theorem sourceRadius_recursive {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ} (hq : Oracle.Total O q) :
    Oracle.Total O (sourceRadius q) := by
  have hh : Oracle.Total O (fun x=>q (Nat.pair ((Nat.unpair x).1+1) (Nat.unpair x).2)) :=
    Oracle.comp hq (Oracle.of_computable (Primrec₂.natPair.comp
      (Primrec.succ.comp (Primrec.fst.comp Primrec.unpair)) (Primrec.snd.comp Primrec.unpair)).to_comp)
  exact hh.of_eq (fun _=>rfl)

theorem targetRadius_recursive {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ} (hq : Oracle.Total O q) :
    Oracle.Total O (targetRadius q) := by
  have hh : Oracle.Total O (fun p=>q (Nat.pair 0 p)) :=
    Oracle.comp hq (Oracle.of_computable (Primrec₂.natPair.comp (Primrec.const 0) Primrec.id).to_comp)
  exact hh.of_eq (fun _=>rfl)

/-- This machine has no dimension, source-count or real-value parameter
in its environment. The runtime input is pair n k. -/
def rawProgramMachine (capacities centres : ℕ → ℕ) (hv : ValidCapacities capacities) : ℕ →. ℕ :=
  programSearch centres (sourceRadius (capacityRadiusCode capacities hv))
    (targetRadius (capacityRadiusCode capacities hv))

theorem rawProgramMachine_recursive {O : Set (ℕ →. ℕ)} {capacities centres : ℕ → ℕ}
    (hv : ValidCapacities capacities) (hcap : Oracle.Total O capacities) (hs : Oracle.Total O centres) :
    Nat.RecursiveIn O (rawProgramMachine capacities centres hv) :=
  programSearch_recursive hs
    (sourceRadius_recursive (capacityRadiusCode_recursive hv hcap))
    (targetRadius_recursive (capacityRadiusCode_recursive hv hcap))

#check_explicit capacityRadiusCode
#check_explicit rawProgramMachine
end SymplecticPacking.Effective.PackingSearch
