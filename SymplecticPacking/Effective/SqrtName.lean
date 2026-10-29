import SymplecticPacking.Effective.NameArithmetic

/-!
# Square-root names

A square-root name from one oracle query and finite integer arithmetic.
-/

namespace SymplecticPacking.Effective.SqrtName
open RationalCode

/-- Four guard bits for the square and two guard bits for its root. -/
def precision (n : ℕ) : ℕ := 2*n+4
def scale (n : ℕ) : ℕ := 2^(n+2)
def clippedNumerator (u : ℕ) : ℕ := positiveNumerator u-negativeNumerator u

def ceiling (u n : ℕ) : ℕ :=
  (clippedNumerator u * scale n ^ 2 + denominator u - 1) / denominator u

/-- Nat.sqrt is an integer algorithm; there is no rational-certificate search. -/
def output (u n : ℕ) : ℕ :=
  encode (Nat.sqrt (ceiling u n)) 0 (scale n-1)

def code (q : ℕ → ℕ) (n : ℕ) : ℕ := output (q (precision n)) n

noncomputable def clippedValue (u : ℕ) : ℝ := (clippedNumerator u : ℝ) / (denominator u : ℝ)

lemma denominator_pos (u : ℕ) : 0 < denominator u := by unfold denominator;omega
lemma scale_pos (n : ℕ) : 0 < scale n := by unfold scale;positivity

lemma clipped_error {u : ℕ} {x e : ℝ} (hx : 0 ≤ x)
    (he : |(value u : ℝ)-x| ≤ e) : |clippedValue u-x| ≤ e := by
  have hd : (0:ℝ)<denominator u := by exact_mod_cast denominator_pos u
  by_cases h : negativeNumerator u ≤ positiveNumerator u
  · have hv : clippedValue u=(value u : ℝ) := by
      simp only [clippedValue,clippedNumerator,Nat.cast_sub h,value,
        Rat.cast_div,Rat.cast_sub,Rat.cast_natCast]
    rwa [hv]
  · have hn : positiveNumerator u < negativeNumerator u := Nat.lt_of_not_ge h
    have hv : (value u : ℝ) ≤ 0 := by
      simp only [value,Rat.cast_div,Rat.cast_sub,Rat.cast_natCast]
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (by exact_mod_cast hn.le)) hd.le
    have hc : clippedValue u=0 := by simp [clippedValue,clippedNumerator,Nat.sub_eq_zero_of_le hn.le]
    rw [hc,zero_sub,abs_neg,abs_of_nonneg hx]
    linarith [(abs_le.mp he).1]

private lemma ceil_nat_bounds (P D : ℕ) (hD : 0<D) :
    P ≤ D*((P+D-1)/D) ∧ D*((P+D-1)/D)<P+D := by
  have ha : P+D-1+1=P+D := by omega
  have h0:=Nat.mul_div_le (P+D-1) D
  have h1:=Nat.lt_mul_div_succ (P+D-1) hD
  simp only [Nat.mul_add,Nat.mul_one] at h1
  omega

lemma ceiling_bounds (u n : ℕ) :
    clippedValue u*(scale n : ℝ)^2 ≤ (ceiling u n : ℝ) ∧
    (ceiling u n : ℝ)<clippedValue u*(scale n : ℝ)^2+1 := by
  have hd : (0:ℝ)<denominator u := by exact_mod_cast denominator_pos u
  obtain ⟨h0,h1⟩:=ceil_nat_bounds (clippedNumerator u*scale n^2) (denominator u)
    (denominator_pos u)
  change _ ≤ denominator u*ceiling u n at h0
  change denominator u*ceiling u n<_ at h1
  have h0r : (clippedNumerator u:ℝ)*(scale n:ℝ)^2 ≤
      (denominator u:ℝ)*(ceiling u n:ℝ) := by exact_mod_cast h0
  have h1r : (denominator u:ℝ)*(ceiling u n:ℝ)<
      (clippedNumerator u:ℝ)*(scale n:ℝ)^2+denominator u := by exact_mod_cast h1
  constructor
  · unfold clippedValue
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hd).2
    nlinarith
  · have hh : (ceiling u n:ℝ)<
        ((clippedNumerator u:ℝ)*(scale n:ℝ)^2+denominator u)/(denominator u:ℝ) :=
      (lt_div_iff₀ hd).2 (by nlinarith)
    have he : ((clippedNumerator u:ℝ)*(scale n:ℝ)^2+denominator u)/(denominator u:ℝ)=
        clippedValue u*(scale n:ℝ)^2+1 := by
      unfold clippedValue
      field_simp
      <;> ring
    rwa [he] at hh

lemma precision_scale (n : ℕ) : (radius (precision n) : ℝ)*(scale n:ℝ)^2=1 := by
  rw [radius_cast]
  simp only [precision,scale,Nat.cast_pow,Nat.cast_ofNat,one_div_pow]
  rw [show 2*n+4=(n+2)*2 by omega,pow_mul]
  field_simp

lemma scale_radius (n : ℕ) : (scale n:ℝ)*(radius n:ℝ)=4 := by
  rw [radius_cast]
  simp only [scale,Nat.cast_pow,Nat.cast_ofNat,one_div_pow,pow_add]
  norm_num
  field_simp

lemma value_output (u n : ℕ) :
    (value (output u n) : ℝ)=(Nat.sqrt (ceiling u n):ℝ)/(scale n:ℝ) := by
  rw [output,value_encode]
  have hd : scale n-1+1=scale n := Nat.sub_add_cancel (by have:=scale_pos n;omega)
  simp only [Nat.cast_zero,sub_zero,Rat.cast_div,Rat.cast_add,Rat.cast_natCast,Rat.cast_one]
  congr 1
  exact_mod_cast hd

/-- The error proof works at x=0 as well as on the strictly positive axis. -/
theorem output_error {u n : ℕ} {x : ℝ} (hx : 0≤x)
    (hu : |(value u:ℝ)-x|≤(radius (precision n):ℝ)) :
    |(value (output u n):ℝ)-Real.sqrt x|≤(radius n:ℝ) := by
  have hd : (0:ℝ)<scale n := by exact_mod_cast scale_pos n
  have hclip:=clipped_error hx hu
  have hlow:=mul_le_mul_of_nonneg_right (abs_le.mp hclip).1 (sq_nonneg (scale n:ℝ))
  have hhigh:=mul_le_mul_of_nonneg_right (abs_le.mp hclip).2 (sq_nonneg (scale n:ℝ))
  have hps:=precision_scale n
  have hceil:=ceiling_bounds u n
  have hk : (0:ℝ)≤Nat.sqrt (ceiling u n) := Nat.cast_nonneg _
  have hsq : (Nat.sqrt (ceiling u n):ℝ)^2≤(ceiling u n:ℝ) := by
    exact_mod_cast Nat.sqrt_le' (ceiling u n)
  have hsq' : (ceiling u n:ℝ)<((Nat.sqrt (ceiling u n):ℝ)+1)^2 := by
    exact_mod_cast Nat.lt_succ_sqrt' (ceiling u n)
  have hs : (0:ℝ)≤(scale n:ℝ)*Real.sqrt x := mul_nonneg hd.le (Real.sqrt_nonneg x)
  have hs2 : ((scale n:ℝ)*Real.sqrt x)^2=x*(scale n:ℝ)^2 := by
    rw [mul_pow,Real.sq_sqrt hx]
    ring
  have hb : |(Nat.sqrt (ceiling u n):ℝ)-(scale n:ℝ)*Real.sqrt x|≤2 := by
    apply abs_le.mpr
    constructor
    · by_contra h
      push_neg at h
      have ht : 0<((scale n:ℝ)*Real.sqrt x-(Nat.sqrt (ceiling u n):ℝ)-2)*
          ((scale n:ℝ)*Real.sqrt x+(Nat.sqrt (ceiling u n):ℝ)+2) :=
        mul_pos (by linarith) (by linarith)
      nlinarith [hceil.2]
    · by_contra h
      push_neg at h
      have ht : 0<((Nat.sqrt (ceiling u n):ℝ)-(scale n:ℝ)*Real.sqrt x-2)*
          ((Nat.sqrt (ceiling u n):ℝ)+(scale n:ℝ)*Real.sqrt x+2) :=
        mul_pos (by linarith) (by linarith)
      nlinarith [hceil.1]
  have hscale : 2/(scale n:ℝ)≤(radius n:ℝ) := by
    apply (div_le_iff₀ hd).2
    nlinarith [scale_radius n]
  rw [value_output]
  have he : (Nat.sqrt (ceiling u n):ℝ)/(scale n:ℝ)-Real.sqrt x=
      ((Nat.sqrt (ceiling u n):ℝ)-(scale n:ℝ)*Real.sqrt x)/(scale n:ℝ) := by
    field_simp
  rw [he,abs_div,abs_of_pos hd]
  exact (div_le_div_of_nonneg_right hb hd.le).trans hscale

theorem code_names {q : ℕ → ℕ} {x : ℝ} (hq : CodeName.Names q x) (hx : 0≤x) :
    CodeName.Names (code q) (Real.sqrt x) :=
  fun n=>output_error hx (hq (precision n))


theorem primitive_precision : Primrec precision :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.id) (Primrec.const 4)

theorem primitive_scale : Primrec scale := by
  exact (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2)
    (Primrec.nat_add.comp Primrec.id (Primrec.const 2))

theorem primitive_clippedNumerator : Primrec clippedNumerator :=
  Primrec.nat_sub.comp primitive_positiveNumerator primitive_negativeNumerator

theorem primitive_ceiling : Primrec (fun a : ℕ×ℕ=>ceiling a.1 a.2) := by
  have hP : Primrec (fun a : ℕ×ℕ=>clippedNumerator a.1) :=
    primitive_clippedNumerator.comp Primrec.fst
  have hD : Primrec (fun a : ℕ×ℕ=>denominator a.1) :=
    primitive_denominator.comp Primrec.fst
  have hd : Primrec (fun a : ℕ×ℕ=>scale a.2) := primitive_scale.comp Primrec.snd
  have hS:=Primrec.nat_mul.comp hd hd
  have hh := Primrec.nat_div.comp
    (Primrec.nat_sub.comp (Primrec.nat_add.comp (Primrec.nat_mul.comp hP hS) hD)
      (Primrec.const 1)) hD
  exact hh.of_eq (fun a=>by simp only [ceiling,pow_two])

theorem primitive_output : Primrec (fun a : ℕ×ℕ=>output a.1 a.2) := by
  have hk:=Primrec.nat_sqrt.comp primitive_ceiling
  have hd : Primrec (fun a : ℕ×ℕ=>scale a.2-1) :=
    Primrec.nat_sub.comp (primitive_scale.comp Primrec.snd) (Primrec.const 1)
  exact Primrec₂.natPair.comp (Primrec₂.natPair.comp hk (Primrec.const 0)) hd

/-- Uniform code evaluation queries precisely the original oracle at the
written precision; its remaining work is primitive recursive integer arithmetic. -/
theorem code_recursive {O : Set (ℕ →. ℕ)} {q : ℕ → ℕ} (hq : Oracle.Total O q) :
    Oracle.Total O (code q) := by
  have hi : Oracle.Total O precision := Oracle.of_computable primitive_precision.to_comp
  have hv:=Oracle.comp hq hi
  have hd:=Oracle.pair hv (Oracle.of_computable Computable.id)
  have hf : Oracle.Total O (fun p=>output (Nat.unpair p).1 (Nat.unpair p).2) :=
    Oracle.of_computable (primitive_output.comp Primrec.unpair).to_comp
  exact (Oracle.comp hf hd).of_eq (fun n=>by simp only [Nat.unpair_pair,code,id_eq])

end SymplecticPacking.Effective.SqrtName
