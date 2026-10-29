import SymplecticPacking.HighDim.Handle.QuadricRationalBoxes

/-!
# Rational codes for quadric coordinate boxes

Rational codes for explicit quadric coordinate boxes.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.Hamiltonian

/-- A box is coded by rational coordinate/radius data, a chart label, and finite root signs. -/
inductive QuadricBoxCode (m : ℕ) where
  | ordinary (q : ℚ × ℚ) (ε : Fin m → Bool) (r : ℚ)
  | branch (i : Fin m) (ε₀ : Bool) (ε : Fin m → Bool) (r : ℚ)

namespace QuadricBoxCode
variable {m : ℕ} (a : Fin m → ℂ)

/-- Validity consists only of a finite list of strict scalar inequalities. -/
def Valid : QuadricBoxCode m → Prop
  | .ordinary q ε r =>
      0 < (r : ℝ) ∧ ordinaryBoxMargin r (ordinaryPresentationCenter a ε (rationalComplex q))
  | .branch i ε₀ ε r =>
      let c := branchPresentationCenter a i ε₀ ε
      0 < (r : ℝ) ∧ (2*(r:ℝ))*(2*‖c.val.2 i‖+2*r) < ‖c.val.1‖^2 ∧
        ∀ j, j≠i → (2*(r:ℝ))*(2*‖c.val.2 i‖+2*r) < ‖c.val.2 j‖^2

theorem ordinary_margin_regular {c : locus a} {r : ℝ} (hr : 0 < r)
    (hm : ordinaryBoxMargin r c) : ∀ j, c.val.2 j ≠ 0 := by
  intro j hj
  have hh := hm j
  have hp : 0 < (2*r)*(2*‖c.val.1‖+2*r) :=
    mul_pos (by positivity) (by positivity)
  rw [hj, norm_zero, zero_pow (by decide)] at hh
  linarith

variable [Fact (Injective a)] [Fact (∀ j, a j ≠ 0)]

/-- Decode a certified box using fixed root formulas. The manifold's selected charts do
not occur in this function. -/
def box (code : QuadricBoxCode m) (h : Valid a code) : RawCoordinateBox (locus a) :=
  match code, h with
  | .ordinary q ε r, h =>
      ordinaryRawBox (ordinaryPresentationCenter a ε (rationalComplex q))
        (ordinary_margin_regular a h.1 h.2) r h.1 h.2
  | .branch i ε₀ ε r, h =>
      branchRawBox (branchPresentationCenter a i ε₀ ε) i
        (branchPresentationCenter_regular a Fact.out Fact.out i ε₀ ε) r h.1 h.2.1 h.2.2

/-- Every point lies in an open inner box with such finite code data. This is a
termination ingredient; it does not replace a finite cover verifier. -/
theorem code_cover (x : locus a) :
    ∃ code : QuadricBoxCode m, ∃ h : Valid a code, x ∈ (box a code h).innerOpen := by
  by_cases hx : ∀ j, x.val.2 j ≠ 0
  · obtain ⟨q, ε, r, hc, hr, hm, hin⟩ := ordinary_rational_boxes_cover x hx
    exact ⟨.ordinary q ε r, ⟨hr, hm⟩, hin⟩
  · push Not at hx
    obtain ⟨i, hi⟩ := hx
    obtain ⟨ε₀, ε, hc⟩ := branchPresentationCenter_complete x i hi
    let c := branchPresentationCenter a i ε₀ ε
    have hreg := branchPresentationCenter_regular a Fact.out Fact.out i ε₀ ε
    obtain ⟨r, hr, hm₀, hm, hin⟩ := branch_centre_rational_box c i hreg
    refine ⟨.branch i ε₀ ε r, ⟨hr, hm₀, hm⟩, ?_⟩
    simpa only [box, c, hc] using hin

end QuadricBoxCode

#check_explicit QuadricBoxCode.box
end SymplecticPacking.HighDim.ToricPackingStages
