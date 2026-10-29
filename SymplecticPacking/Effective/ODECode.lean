import SymplecticPacking.Effective.ODE
import SymplecticPacking.Effective.NameArithmetic
import SymplecticPacking.Explicit

/-!
# Coded rational Euler programs

Finite rational Euler programs relative only to field-value names: state codes, one exact
Euler update and its iteration.
-/

namespace SymplecticPacking.Effective.ODECode
open RationalCode
open scoped Classical
set_option maxHeartbeats 1600000

abbrev State (d : ℕ) := Fin d → ℕ

local instance (d : ℕ) : Encodable (State d) := Primcodable.toEncodable

/-- Public encoder matching the primitive-recursive state decoder. -/
def encodeState (d : ℕ) (x : State d) : ℕ := Encodable.encode x

def decodeState (d c : ℕ) : State d :=
  (Encodable.decode (α := State d) c).getD (fun _ => zeroCode)

@[simp] theorem decodeState_encodeState (d : ℕ) (x : State d) :
    decodeState d (encodeState d x) = x := by simp [decodeState, encodeState]

def rationalState {d : ℕ} (x : State d) : Fin d → ℚ := fun j => value (x j)
def realState {d : ℕ} (x : State d) : Fin d → ℝ := fun j => (value (x j) : ℝ)

@[simp] theorem decodeState_encode (d : ℕ) (x : State d) :
    decodeState d (Encodable.encode x) = x := by simp [decodeState]

/-- One exact rational Euler update, performed by natural-code arithmetic. -/
def update (d N : ℕ) (x v : State d) : State d :=
  fun j => addCode (x j) (divideNatCode (v j) (N-1))

/-- Rational time `i/N`, without a rational-number encoding search. -/
def timeCode (N i : ℕ) : ℕ := encode i 0 (N-1)

/-- The field oracle receives `(time code,(state code,requested precision))`.
Its result is one code for the finite vector of rational field values. -/
def step (d N p : ℕ) (field : ℕ → ℕ) (i state : ℕ) : ℕ :=
  Encodable.encode (update d N (decodeState d state)
    (decodeState d (field (Nat.pair (timeCode N i) (Nat.pair state p)))))

def iterate (d N p : ℕ) (field : ℕ → ℕ) (initial : ℕ) : ℕ → ℕ
  | 0 => initial
  | i+1 => step d N p field i (iterate d N p field initial i)

/-- A program input encodes `(mesh size,precision)`. No solution-name oracle occurs. -/
def run (d : ℕ) (field initial : ℕ → ℕ) (a : ℕ) : ℕ :=
  iterate d (Nat.unpair a).1 (Nat.unpair a).2 field (initial (Nat.unpair a).2) (Nat.unpair a).1

theorem timeCode_value {N : ℕ} (hN : 0 < N) (i : ℕ) :
    value (timeCode N i) = (i:ℚ)/N := by
  rw [timeCode, value_encode]
  have hden : ((N-1:ℕ):ℚ)+1 = N := by exact_mod_cast Nat.sub_add_cancel hN
  simp only [Nat.cast_zero, sub_zero, hden]

theorem update_value {d N : ℕ} (hN : 0 < N) (x v : State d) (j : Fin d) :
    value (update d N x v j) = value (x j)+value (v j)/(N:ℚ) := by
  rw [update, value_addCode, value_divideNatCode]
  congr 2
  exact_mod_cast Nat.sub_add_cancel hN

theorem update_real {d N : ℕ} (hN : 0 < N) (x v : State d) :
    realState (update d N x v) = realState x+(1/(N:ℝ)) • realState v := by
  funext j
  change (value (update d N x v j):ℝ) = (value (x j):ℝ)+(1/(N:ℝ))*(value (v j):ℝ)
  rw [update_value hN]
  push_cast
  ring

theorem primitive_timeCode : Primrec₂ timeCode :=
  Primrec₂.natPair.comp (Primrec₂.natPair.comp Primrec.snd (Primrec.const 0))
    (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1))

def solution (d L C : ℕ) (field initial : ℕ → ℕ) (n : ℕ) : ℕ :=
  run d field initial (Nat.pair (ODE.mesh L C n) (ODE.precision L n))

#check_explicit solution
#check_explicit iterate
end SymplecticPacking.Effective.ODECode
