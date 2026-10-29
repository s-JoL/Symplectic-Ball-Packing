import SymplecticPacking.Effective.Integral
import SymplecticPacking.Effective.Family

/-!
# Coded quadrature

Finite coded quadrature, uniformly in parameters, using only integrand-value names.
-/

namespace SymplecticPacking.Effective.QuadratureCode
open RationalCode
open Set MeasureTheory
open scoped BigOperators

def timeCode (N i : ℕ) : ℕ := encode i 0 (N-1)

/-- Query layout is `((parameter,rational time code),precision)`. -/
def sample (q : ℕ → ℕ) (c N p i : ℕ) : ℕ :=
  q (Nat.pair (Nat.pair c (timeCode N i)) p)

def sum (q : ℕ → ℕ) (c N p : ℕ) : ℕ → ℕ
  | 0 => zeroCode
  | i+1 => addCode (sum q c N p i) (sample q c N p i)

/-- Finite input `a` encodes `(parameter,(mesh,query precision))`. -/
def run (q : ℕ → ℕ) (a : ℕ) : ℕ :=
  let c := (Nat.unpair a).1
  let N := (Nat.unpair (Nat.unpair a).2).1
  let p := (Nat.unpair (Nat.unpair a).2).2
  divideNatCode (sum q c N p N) (N-1)

/-- The mesh bound is finite data attached to each parameter. -/
def family (q : ℕ → ℕ) (K : ℕ → ℕ) (a : ℕ) : ℕ :=
  let c := (Nat.unpair a).1
  let n := (Nat.unpair a).2
  run q (Nat.pair c (Nat.pair (Quadrature.mesh (K c) n) (n+1)))

theorem timeCode_value {N : ℕ} (hN : 0 < N) (i : ℕ) :
    value (timeCode N i) = (i:ℚ)/N := by
  rw [timeCode, value_encode]
  have he : ((N-1:ℕ):ℚ)+1=N := by exact_mod_cast Nat.sub_add_cancel hN
  simp only [Nat.cast_zero, sub_zero, he]

theorem sum_value (q : ℕ → ℕ) (c N p i : ℕ) :
    value (sum q c N p i) = ∑ j ∈ Finset.range i, value (sample q c N p j) := by
  induction i with
  | zero => simp only [sum, value_zeroCode, Finset.range_zero, Finset.sum_empty]
  | succ i ih => rw [sum, value_addCode, Finset.sum_range_succ, ih]

theorem run_value (q : ℕ → ℕ) (c N p : ℕ) (hN : 0 < N) :
    value (run q (Nat.pair c (Nat.pair N p))) =
      (∑ i ∈ Finset.range N, value (sample q c N p i))/(N:ℚ) := by
  simp only [run, Nat.unpair_pair, value_divideNatCode, sum_value]
  congr 1
  exact_mod_cast Nat.sub_add_cancel hN

/-- A uniform name of the original integrand at rational inputs. -/
def ValueNames (q : ℕ → ℕ) (f : ℕ → ℝ → ℝ) : Prop :=
  ∀ c t, CodeName.Names (fun p => q (Nat.pair (Nat.pair c t) p)) (f c (value t))

theorem run_error {q : ℕ → ℕ} {f : ℕ → ℝ → ℝ} (hq : ValueNames q f)
    (c N p : ℕ) (hN : 0 < N) :
    |(value (run q (Nat.pair c (Nat.pair N p))):ℝ)-Quadrature.realSum (f c) N| ≤ (radius p:ℝ) := by
  rw [run_value q c N p hN, Rat.cast_div, Rat.cast_natCast]
  apply Quadrature.samples_error _ hN
  intro i hi
  have hs := hq c (timeCode N i) p
  rw [timeCode_value hN, Rat.cast_div, Rat.cast_natCast] at hs
  exact hs

/-- A true integral name follows from compact-interval Lipschitz bounds and only
point-value names. Neither the program nor its recursion proof queries an integral. -/
theorem family_names {q K : ℕ → ℕ} {f : ℕ → ℝ → ℝ} (hq : ValueNames q f)
    (hf : ∀ c, Continuous (f c))
    (hlip : ∀ c, ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1,
      |f c x-f c y| ≤ (2:ℝ)^(K c)*|x-y|) :
    Family.Names (family q K) (fun c => ∫ x in (0:ℝ)..1, f c x) := by
  intro c n
  change |(value (family q K (Nat.pair c n)):ℝ)-(∫ x in (0:ℝ)..1, f c x)| ≤ _
  simp only [family, Nat.unpair_pair, id_eq]
  have hs := run_error hq c (Quadrature.mesh (K c) n) (n+1) (Quadrature.mesh_pos _ _)
  have hi := Quadrature.realSum_error (hf c) (by positivity : (0:ℝ) ≤ 2^(K c))
    (hlip c) (Quadrature.mesh_pos (K c) n)
  have hm := Quadrature.mesh_error (L := (2:ℝ)^(K c)) le_rfl n
  have ht := abs_sub_le (value (run q (Nat.pair c (Nat.pair (Quadrature.mesh (K c) n) (n+1)))):ℝ)
    (Quadrature.realSum (f c) (Quadrature.mesh (K c) n)) (∫ x in (0:ℝ)..1, f c x)
  rw [abs_sub_comm (Quadrature.realSum (f c) (Quadrature.mesh (K c) n))] at ht
  have hr : (radius (n+1):ℝ)=(radius n:ℝ)/2 := by exact_mod_cast radius_succ n
  change |(value (run q (Nat.pair c (Nat.pair (Quadrature.mesh (K c) n) (n+1)))):ℝ)-
    (∫ x in (0:ℝ)..1, f c x)| ≤ _
  linarith

theorem primitive_timeCode : Primrec₂ timeCode :=
  Primrec₂.natPair.comp (Primrec₂.natPair.comp Primrec.snd (Primrec.const 0))
    (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1))

theorem primitive_mesh : Primrec₂ Quadrature.mesh := by
  have he : Primrec (fun a : ℕ × ℕ => a.2+a.1+1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.snd Primrec.fst) (Primrec.const 1)
  exact (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2) he

/-- One loop step queries the original uniform integrand evaluator. -/
theorem step_recursive {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ} (hq : Oracle.Total O q) :
    Oracle.Total O (fun b => addCode (Nat.unpair (Nat.unpair b).2).2
      (sample q (Nat.unpair (Nat.unpair b).1).1
        (Nat.unpair (Nat.unpair (Nat.unpair b).1).2).1
        (Nat.unpair (Nat.unpair (Nat.unpair b).1).2).2
        (Nat.unpair (Nat.unpair b).2).1)) := by
  have ha := Oracle.left (O := O)
  have hc := Oracle.comp Oracle.left ha
  have hNp := Oracle.comp Oracle.right ha
  have hN := Oracle.comp Oracle.left hNp
  have hp := Oracle.comp Oracle.right hNp
  have hi := Oracle.comp Oracle.left (Oracle.right (O := O))
  have hx := Oracle.comp Oracle.right (Oracle.right (O := O))
  have ht := Oracle.comp (Oracle.of_computable (primitive_timeCode.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp) (Oracle.pair hN hi)
  have hv := Oracle.comp hq (Oracle.pair (Oracle.pair hc ht) hp)
  exact (Oracle.comp (Oracle.of_computable (primitive_addCode.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp)
      (Oracle.pair hx hv)).of_eq (fun b => by simp only [sample, Nat.unpair_pair])

theorem run_recursive {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ} (hq : Oracle.Total O q) :
    Oracle.Total O (run q) := by
  have hloop := Oracle.prec (Oracle.of_computable (Computable.const zeroCode)) (step_recursive hq)
  have heq (a i : ℕ) : i.rec zeroCode
      (fun j x => addCode x (sample q (Nat.unpair a).1
        (Nat.unpair (Nat.unpair a).2).1 (Nat.unpair (Nat.unpair a).2).2 j)) =
      sum q (Nat.unpair a).1 (Nat.unpair (Nat.unpair a).2).1
        (Nat.unpair (Nat.unpair a).2).2 i := by
    induction i with
    | zero => rfl
    | succ i ih => exact congrArg (fun x => addCode x (sample q _ _ _ i)) ih
  have hsum : Oracle.Total O (fun b => sum q (Nat.unpair (Nat.unpair b).1).1
      (Nat.unpair (Nat.unpair (Nat.unpair b).1).2).1
      (Nat.unpair (Nat.unpair (Nat.unpair b).1).2).2 (Nat.unpair b).2) :=
    hloop.of_eq (fun b => by
      simp only [Nat.unpair_pair]
      exact congrArg Part.some (heq (Nat.unpair b).1 (Nat.unpair b).2))
  have hc := Oracle.left (O := O)
  have hN := Oracle.comp Oracle.left (Oracle.right (O := O))
  have hp := Oracle.comp Oracle.right (Oracle.right (O := O))
  have hsumN := Oracle.comp hsum (Oracle.pair (Oracle.of_computable Computable.id) hN)
  have hden := Oracle.comp (Oracle.of_computable
    (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)).to_comp) hN
  exact (Oracle.comp (Oracle.of_computable (primitive_divideNatCode.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp)
      (Oracle.pair hsumN hden)).of_eq (fun a => by simp only [run, Nat.unpair_pair, id_eq])

/-- Both the geometric parameter and requested digit are input. The supplied
mesh-bound function is itself reduced to the same original oracles. -/
theorem family_recursive {O : Set (ℕ →. ℕ)} {q K : ℕ → ℕ}
    (hq : Oracle.Total O q) (hK : Oracle.Total O K) : Oracle.Total O (family q K) := by
  have hc := Oracle.left (O := O)
  have hn := Oracle.right (O := O)
  have hkc := Oracle.comp hK hc
  have hN := Oracle.comp (Oracle.of_computable (primitive_mesh.comp
    (Primrec.fst.comp Primrec.unpair) (Primrec.snd.comp Primrec.unpair)).to_comp)
      (Oracle.pair hkc hn)
  have hp := Oracle.comp (Oracle.of_computable (Primrec.nat_add.comp Primrec.id (Primrec.const 1)).to_comp) hn
  exact (Oracle.comp (run_recursive hq) (Oracle.pair hc (Oracle.pair hN hp))).of_eq
    (fun a => by simp only [family, Nat.unpair_pair, id_eq])

#check_explicit family
end SymplecticPacking.Effective.QuadratureCode
