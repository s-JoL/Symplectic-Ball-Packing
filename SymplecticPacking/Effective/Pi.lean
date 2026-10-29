import SymplecticPacking.Effective.IntegralCode
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A name of π

A name of π from finite rational quadrature of 4/(1+t²).
-/

namespace SymplecticPacking.Effective.Pi
open RationalCode Set
open scoped BigOperators

noncomputable def integrand (t : ℝ) : ℝ := 4/(1+t^2)

theorem integrand_continuous : Continuous integrand :=
  continuous_const.div (continuous_const.add (continuous_id.pow 2)) (fun t => by positivity)

theorem integrand_lipschitz {x y : ℝ} (hx : x ∈ Icc (0:ℝ) 1) (hy : y ∈ Icc (0:ℝ) 1) :
    |integrand x-integrand y| ≤ 8*|x-y| := by
  have hd1 : 0 < 1+x^2 := by positivity
  have hd2 : 0 < 1+y^2 := by positivity
  have hdp : 0 < (1+x^2)*(1+y^2) := mul_pos hd1 hd2
  have hd : 1 ≤ (1+x^2)*(1+y^2) := by nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  have he : integrand x-integrand y=4*(y-x)*(y+x)/((1+x^2)*(1+y^2)) := by
    unfold integrand
    field_simp [hd1.ne', hd2.ne']
    ring
  rw [he, abs_div, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4),
    abs_of_nonneg (by linarith [hy.1, hx.1] : 0 ≤ y+x), abs_sub_comm y x,
    abs_of_pos hdp, div_le_iff₀ hdp]
  calc
    _ ≤ 4*|x-y| *2 := by gcongr; linarith [hx.2, hy.2]
    _ = 8*|x-y| := by ring
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hd

theorem integral_integrand : (∫ t in (0:ℝ)..1, integrand t)=Real.pi := by
  have he : integrand = fun t : ℝ => 4*(1/(1+t^2)) := by funext t; unfold integrand; ring
  rw [he, intervalIntegral.integral_const_mul, integral_one_div_one_add_sq,
    Real.arctan_one, Real.arctan_zero, sub_zero]
  ring

def oneCode : ℕ := encode 1 0 0
def fourCode : ℕ := encode 4 0 0

def integrandCode (u : ℕ) : ℕ :=
  mulCode fourCode (invCode (addCode oneCode (mulCode u u)))

theorem integrandCode_value (u : ℕ) : (value (integrandCode u):ℝ)=integrand (value u) := by
  simp only [integrandCode, value_mulCode, value_invCode, value_addCode,
    fourCode, oneCode, value_encode, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, sub_zero,
    zero_add, div_one, Rat.cast_mul, Rat.cast_inv, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat,
    integrand, pow_two, div_eq_mul_inv, inv_one, mul_one, one_mul]

def values (a : ℕ) : ℕ := integrandCode (Nat.unpair (Nat.unpair a).1).2

theorem values_names : QuadratureCode.ValueNames values (fun _ => integrand) := by
  intro c t n
  change |(value (values (Nat.pair (Nat.pair c t) n)):ℝ)-integrand (value t)| ≤ _
  rw [values, Nat.unpair_pair, Nat.unpair_pair, integrandCode_value, sub_self, abs_zero]
  exact_mod_cast (radius_pos n).le

def name (n : ℕ) : ℕ := QuadratureCode.family values (fun _ => 3) (Nat.pair 0 n)

theorem name_spec : CodeName.Names name Real.pi := by
  have hq := QuadratureCode.family_names (K := fun _ => 3) values_names (fun _ => integrand_continuous) (by
    intro c x hx y hy
    norm_num
    exact integrand_lipschitz hx hy)
  intro n
  simpa only [name, Family.slice, integral_integrand] using hq 0 n

theorem primitive_integrandCode : Primrec integrandCode :=
  primitive_mulCode.comp (Primrec.const fourCode)
    (primitive_invCode.comp (primitive_addCode.comp (Primrec.const oneCode)
      (primitive_mulCode.comp Primrec.id Primrec.id)))

theorem name_recursive {O : Set (ℕ →. ℕ)} : Oracle.Total O name := by
  have hv : Oracle.Total O values := Oracle.of_computable
    (primitive_integrandCode.comp (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.fst.comp Primrec.unpair)))).to_comp
  have hf := QuadratureCode.family_recursive hv (Oracle.of_computable (Computable.const 3))
  exact (Oracle.comp hf (Oracle.pair (Oracle.of_computable (Computable.const 0))
    (Oracle.of_computable Computable.id))).of_eq (fun n => rfl)

def family (a : ℕ) : ℕ := name (Nat.unpair a).2

theorem family_names : Family.Names family (fun _ => Real.pi) := by
  intro c n
  simpa only [Family.slice, family, Nat.unpair_pair] using name_spec n

theorem family_recursive {O : Set (ℕ →. ℕ)} : Oracle.Total O family :=
  (Oracle.comp (name_recursive (O := O)) (Oracle.right (O := O))).of_eq (fun a => rfl)

end SymplecticPacking.Effective.Pi
