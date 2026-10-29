import SymplecticPacking.Effective.FiniteGrid
import SymplecticPacking.Effective.PackingCertificateInput

/-!
# The rational covering grid

The rational covering grid on a runtime integer source box.
-/

namespace SymplecticPacking.Effective.PackingCertificate
open RationalCode
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def boxNode (d Q m i : ℕ) : Fin d → ℚ :=
  fun j => 2*(Q:ℚ)*FiniteGrid.node d m i j-Q

def boxRadius (Q m : ℕ) : ℚ := 2*(Q:ℚ)*radius m

theorem box_covered (d Q m : ℕ) (hQ : 0<Q) (x : Fin d → ℝ)
    (hx : ∀ j, |x j|≤(Q:ℝ)) :
    ∃ i<FiniteGrid.count d m, ‖x-ODE.castVector (boxNode d Q m i)‖≤(boxRadius Q m:ℝ) := by
  have hQ' : (0:ℝ)<Q := by exact_mod_cast hQ
  let y : Fin d → ℝ := fun j => (x j+Q)/(2*(Q:ℝ))
  have hy : ∀ j, y j∈Set.Icc (0:ℝ) 1 := by
    intro j
    have hh := abs_le.mp (hx j)
    exact ⟨div_nonneg (by linarith) (by positivity),
      (div_le_one (by positivity : (0:ℝ)<2*Q)).mpr (by linarith)⟩
  obtain ⟨i,hi,hcover⟩ := FiniteGrid.cube_covered d m y hy
  refine ⟨i,hi,?_⟩
  have heq : x-ODE.castVector (boxNode d Q m i) =
      (2*(Q:ℝ)) • (y-FiniteGrid.realNode d m i) := by
    funext j
    simp only [Pi.sub_apply, ODE.castVector, boxNode, Rat.cast_sub, Rat.cast_mul,
      Rat.cast_ofNat, Rat.cast_natCast, Pi.smul_apply, smul_eq_mul, y, FiniteGrid.realNode]
    field_simp [hQ'.ne']
    ring
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ)<2*Q)]
  simpa only [boxRadius, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast] using
    mul_le_mul_of_nonneg_left hcover (by positivity : (0:ℝ)≤2*Q)

def boxNodeState (d Q m i : ℕ) : ODECode.State d := fun j =>
  addCode (mulCode (encode (2*Q) 0 0) (ODECode.decodeState d (FiniteGrid.code d m i) j))
    (negCode (encode Q 0 0))

def boxNodeCode (d Q m i : ℕ) : ℕ := ODECode.encodeState d (boxNodeState d Q m i)

theorem boxNodeState_value (d Q m i : ℕ) :
    ODECode.rationalState (boxNodeState d Q m i)=boxNode d Q m i := by
  funext j
  simp [boxNodeState, ODECode.rationalState, FiniteGrid.code_decode, FiniteGrid.node,
    boxNode, value_addCode, value_mulCode, value_negCode, value_encode, sub_eq_add_neg]

end SymplecticPacking.Effective.PackingCertificate
