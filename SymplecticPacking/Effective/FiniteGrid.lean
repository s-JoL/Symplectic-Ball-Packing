import SymplecticPacking.Effective.ODECode

/-!
# Finite dyadic grids

Canonical finite dyadic grids, with machine codes and a closed-cube covering theorem.
-/

namespace SymplecticPacking.Effective.FiniteGrid
open RationalCode

/-- Base-`B` digits in canonical coordinate order. -/
def digits : (d : ℕ) → ℕ → ℕ → Fin d → ℕ
  | 0, _, _, j => Fin.elim0 j
  | d+1, B, i, j => Fin.cases (i % B) (digits d B (i/B)) j

def index : (d : ℕ) → ℕ → (Fin d → ℕ) → ℕ
  | 0, _, _ => 0
  | d+1, B, v => v 0+B*index d B (fun j => v j.succ)

lemma digits_index (d B : ℕ) (hB : 0<B) (v : Fin d → ℕ) (hv : ∀ j,v j<B) :
    digits d B (index d B v)=v := by
  induction d with
  | zero => exact funext (fun j => Fin.elim0 j)
  | succ d ih =>
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [index,digits,Fin.cases_zero,Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (hv 0)]
      · simp only [index,digits,Fin.cases_succ,Nat.add_mul_div_left _ _ hB,
          Nat.div_eq_of_lt (hv 0),zero_add]
        exact congrFun (ih (fun j => v j.succ) (fun j => hv j.succ)) j

lemma index_lt (d B : ℕ) (hB : 0<B) (v : Fin d → ℕ) (hv : ∀ j,v j<B) :
    index d B v < B^d := by
  induction d with
  | zero => simp only [index,pow_zero]; omega
  | succ d ih =>
      have hh := ih (fun j => v j.succ) (fun j => hv j.succ)
      have hz := hv 0
      simp only [index,pow_succ]
      nlinarith

def size (m : ℕ) : ℕ := 2^m
def count (d m : ℕ) : ℕ := (size m+1)^d

def nodeCodes (d m i : ℕ) : ODECode.State d :=
  fun j => ODECode.timeCode (size m) (digits d (size m+1) i j)

def node (d m i : ℕ) : Fin d → ℚ := fun j => value (nodeCodes d m i j)
def realNode (d m i : ℕ) : Fin d → ℝ := fun j => (node d m i j:ℝ)
def code (d m i : ℕ) : ℕ := ODECode.encodeState d (nodeCodes d m i)

lemma size_pos (m : ℕ) : 0<size m := pow_pos (by omega) _

lemma node_value (d m i : ℕ) (j : Fin d) :
    node d m i j = (digits d (size m+1) i j:ℚ)/size m :=
  ODECode.timeCode_value (size_pos m) _

lemma reciprocal_size (m : ℕ) : (1:ℝ)/(size m:ℝ)=(radius m:ℝ) := by
  simp only [size,Nat.cast_pow,Nat.cast_ofNat,radius_cast,div_pow,one_pow]

/-- Every point of the closed unit cube is covered at the requested dyadic accuracy.
The witness index is used only in the proof; the evaluated grid itself is finite natural data. -/
theorem cube_covered (d m : ℕ) (x : Fin d → ℝ) (hx : ∀ j,x j∈Set.Icc (0:ℝ) 1) :
    ∃ i<count d m, ‖x-realNode d m i‖≤(radius m:ℝ) := by
  let N := size m
  let v : Fin d → ℕ := fun j => ⌊(N:ℝ)*x j⌋₊
  have hN : (0:ℝ)<N := by exact_mod_cast size_pos m
  have hv : ∀ j,v j<N+1 := by
    intro j
    have hf := Nat.floor_le (mul_nonneg hN.le (hx j).1)
    have hh : (v j:ℝ) ≤ N := hf.trans (by nlinarith [(hx j).2])
    have hhN : v j≤N := by exact_mod_cast hh
    omega
  refine ⟨index d (N+1) v,index_lt d (N+1) (by omega) v hv,?_⟩
  apply (pi_norm_le_iff_of_nonneg (by exact_mod_cast (radius_pos m).le)).mpr
  intro j
  have he : realNode d m (index d (N+1) v) j=(v j:ℝ)/N := by
    rw [realNode,node_value]
    rw [show size m=N from rfl,digits_index d (N+1) (by omega) v hv]
    push_cast
    rfl
  simp only [Pi.sub_apply,Real.norm_eq_abs,he]
  rw [← reciprocal_size m]
  change |x j-(v j:ℝ)/N|≤1/(N:ℝ)
  have hf : (v j:ℝ) ≤ (N:ℝ)*x j := Nat.floor_le (mul_nonneg hN.le (hx j).1)
  have hg := Nat.lt_floor_add_one ((N:ℝ)*x j)
  have hlo : 0≤x j-(v j:ℝ)/N := by
    have hh : (v j:ℝ)/N≤x j := (div_le_iff₀ hN).mpr (by nlinarith [hf])
    linarith
  rw [abs_of_nonneg hlo]
  apply (le_div_iff₀ hN).mpr
  have hcancel : (x j-(v j:ℝ)/N)*(N:ℝ)=(N:ℝ)*x j-v j := by
    field_simp [hN.ne'] <;> ring
  rw [hcancel]
  change (N:ℝ)*x j-(v j:ℝ)≤1
  change (N:ℝ)*x j<(v j:ℝ)+1 at hg
  linarith

lemma code_decode (d m i : ℕ) : ODECode.decodeState d (code d m i)=nodeCodes d m i :=
  ODECode.decodeState_encodeState _ _

theorem primitive_size : Primrec size :=
  (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp (Primrec.const 2) Primrec.id

end SymplecticPacking.Effective.FiniteGrid
