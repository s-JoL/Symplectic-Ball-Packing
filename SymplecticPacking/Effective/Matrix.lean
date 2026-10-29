import SymplecticPacking.Effective.Family
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Reciprocal names

A finite program for a name of `1/x` from a name of `x` and a certified bound `2⁻ᵏ ≤ |x|`.
-/

namespace SymplecticPacking.Effective.Matrix
open RationalCode

/-- Certified `2⁻ᵏ ≤ |x|` gives a fixed finite query precision for the reciprocal.
The runtime inputs are the original name and the natural certificate `k`. -/
def reciprocal (q k : ℕ → ℕ) (p : ℕ) : ℕ :=
  let c := (Nat.unpair p).1
  let n := (Nat.unpair p).2
  invCode (q (Nat.pair c (n+2*k c+2)))

lemma radius_le_one (n : ℕ) : (radius n:ℝ) ≤ 1 := by
  rw [radius_cast]
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma reciprocal_names {q k : ℕ → ℕ} {x : ℕ → ℝ} (hq : Family.Names q x)
    (hk : ∀ c, (radius (k c):ℝ) ≤ |x c|) :
    Family.Names (reciprocal q k) (fun c => (x c)⁻¹) := by
  intro c n
  let δ : ℝ := radius (k c)
  let r : ℝ := radius n
  let y : ℝ := value (q (Nat.pair c (n+2*k c+2)))
  have hδ : 0 < δ := by
    change 0 < (radius (k c):ℝ)
    exact_mod_cast radius_pos (k c)
  have hδ1 : δ ≤ 1 := radius_le_one _
  have hr : 0 ≤ r := by
    change 0 ≤ (radius n:ℝ)
    exact_mod_cast (radius_pos n).le
  have hr1 : r ≤ 1 := radius_le_one _
  have hshift : (radius (n+2*k c+2):ℝ)=r*δ^2/4 := by
    dsimp only [r,δ]
    rw [show n+2*k c+2=n+(k c+k c)+2 by omega]
    simp only [radius_cast,pow_add]
    norm_num
    ring
  have he : |y-x c| ≤ r*δ^2/4 := by
    simpa only [Family.slice,hshift] using hq c (n+2*k c+2)
  have hsq : δ^2 ≤ δ := by nlinarith
  have hmul : r*δ^2 ≤ δ :=
    (mul_le_of_le_one_left (sq_nonneg δ) hr1).trans hsq
  have hsmall : |y-x c| ≤ δ/4 := he.trans (by linarith)
  have htriangle : |x c| ≤ |x c-y|+|y| := by
    calc |x c| = |(x c-y)+y| := by ring_nf
         _ ≤ |x c-y|+|y| := by simpa only [Real.norm_eq_abs] using norm_add_le (x c-y) y
  have hy : δ/2 ≤ |y| := by
    rw [abs_sub_comm] at hsmall
    have hh := hk c
    change δ ≤ |x c| at hh
    linarith
  have hprod : δ^2/2 ≤ |y| *|x c| := by
    have hh := mul_le_mul hy (hk c) hδ.le (abs_nonneg y)
    nlinarith
  have hxnz : x c ≠ 0 := abs_pos.mp (hδ.trans_le (hk c))
  have hynz : y ≠ 0 := abs_pos.mp (lt_of_lt_of_le (by positivity : 0<δ/2) hy)
  change |(value (reciprocal q k (Nat.pair c n)):ℝ)-(x c)⁻¹| ≤ r
  simp only [reciprocal,Nat.unpair_pair,value_invCode,Rat.cast_inv]
  change |y⁻¹-(x c)⁻¹| ≤ r
  rw [inv_sub_inv hynz hxnz,abs_div,abs_mul,
    div_le_iff₀ (mul_pos (abs_pos.mpr hynz) (abs_pos.mpr hxnz))]
  rw [abs_sub_comm]
  have hh := mul_le_mul_of_nonneg_left hprod hr
  nlinarith [mul_nonneg hr (sq_nonneg δ)]

lemma reciprocal_recursive {O : Set (ℕ →. ℕ)} {q k : ℕ → ℕ}
    (hq : Oracle.Total O q) (hk : Oracle.Total O k) :
    Oracle.Total O (reciprocal q k) := by
  have hp : Primrec (fun p : ℕ => (Nat.unpair p).1+2*(Nat.unpair p).2+2) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.fst.comp Primrec.unpair)
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.unpair))) (Primrec.const 2)
  have hprecision := Oracle.comp (Oracle.of_computable hp.to_comp)
    (Oracle.pair (Oracle.right (O:=O)) (Oracle.comp hk (Oracle.left (O:=O))))
  have hv := Oracle.comp hq (Oracle.pair (Oracle.left (O:=O)) hprecision)
  exact (Oracle.comp (Oracle.of_computable primitive_invCode.to_comp) hv).of_eq
    (fun p => by simp only [reciprocal,Nat.unpair_pair])

end SymplecticPacking.Effective.Matrix
