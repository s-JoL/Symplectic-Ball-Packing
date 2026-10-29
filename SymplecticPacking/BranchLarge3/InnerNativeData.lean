import SymplecticPacking.BranchLarge3.ComparisonData
import SymplecticPacking.BranchLarge3.Weights
import SymplecticPacking.HighDim.Handle.NativeProfile
import SymplecticPacking.HighDim.Handle.CubicRawTotalModel
import SymplecticPacking.HighDim.Handle.CubicRawProvider
import SymplecticPacking.HighDim.Handle.QuadricFlowAtlas

/-!
# Data of the six-dimensional inner packing

Native data of the six-dimensional inner packing. The construction uses only
comparison scalars, finite polyhedral data, ambient forms, and the certified raw atlas.
-/

noncomputable section
namespace SymplecticPacking.BranchLarge3.NativeInner
open Set MeasureTheory
open HighDim HighDim.ToricPackingStages
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.MomentPolytope
variable {N : ℕ}

def weights (Q : ℕ) (r : Fin N → ℝ) (a : ℚ) : Weights :=
  BranchLarge3.weights Q a (cmpData r a).e (cmpData r a).d₂

def coefficient (Q : ℕ) (r : Fin N → ℝ) (a : ℚ) : ℝ :=
  1/((weights Q r a).L*Real.pi)

def polytope (r : Fin N → ℝ) (a : ℚ) : HighDim.Polytope 2 2 :=
  ⟨sixModelBounds,![((cmpData r a).h₁:ℝ),(cmpData r a).h₂]⟩

def area (Q : ℕ) (r : Fin N → ℝ) (a : ℚ) : Moments 2 → ℝ :=
  physicalArea (weights Q r a).D (weights Q r a).S (coefficient Q r a) (weights Q r a).L

def areaPoly (Q : ℕ) (r : Fin N → ℝ) (a : ℚ) : PolyFn 2 :=
  let W := weights Q r a
  let c := coefficient Q r a
  [⟨fun _ => 7*c*Real.pi*W.L,c*Real.pi*(2*(W.S:ℝ)-3*(W.D:ℝ))⟩,
   ⟨fun _ => 9*c*Real.pi*W.L,-3*c*Real.pi*(W.D:ℝ)⟩]

def tolerance (Q : ℕ) (r : Fin N → ℝ) (a : ℚ) : ℝ :=
  NativeProfile.tolerance (polytope r a) (area Q r a) r (cmpData r a).ε

def negativeProfile (Q : ℕ) (r : Fin N → ℝ) (a : ℚ) : PolyFn 2 :=
  Surf.negPolyOf (areaPoly Q r a) r (tolerance Q r a)

def input (Q : ℕ) (r : Fin N → ℝ) (a : ℚ) : CmpInput 2 2 :=
  NativeProfile.input (polytope r a) (negativeProfile Q r a) (cmpData r a).τ (cmpData r a).ε

def datum (Q : ℕ) (r : Fin N → ℝ) (a : ℚ) : ComparisonDatum 2 :=
  (input Q r a).comparatorDatum (negativeProfile Q r a)

def level (Q : ℕ) (r : Fin N → ℝ) (a : ℚ) : ℕ :=
  let W := weights Q r a
  let c := coefficient Q r a
  cubicRawLevel (cubicAreaModulusFormula W.A W.B W.D W.S W.L c
    (cmpData r a).h₁ (cmpData r a).h₂ (tolerance Q r a))
    W.A W.B W.D W.S W.L c (cmpData r a).h₁ (cmpData r a).h₂ (datum Q r a).reserve

def rawModel (Q : ℕ) (r : Fin N → ℝ) (a : ℚ) :=
  let W := weights Q r a
  cubicRawTotalModel W.A W.B W.D W.S (coefficient Q r a) W.L 2 (level Q r a) (polytope r a)

def maps (Q : ℕ) (r r' : Fin N → ℝ) (a : ℚ) :
    Fin N → Ambient 3 → BaseCurve × HighDim.Fibre 2 :=
  (rawModel Q r a).packing (quadricFlowAtlas 0 (level Q r a)) (datum Q r a) r r'

theorem areaPoly_ne_nil (Q : ℕ) (r : Fin N → ℝ) (a : ℚ) : areaPoly Q r a≠[] := by
  simp [areaPoly]

theorem area_eq_poly (Q : ℕ) (r : Fin N → ℝ) (a : ℚ) (hc : 0 ≤ coefficient Q r a)
    (p : Moments 2) : area Q r a p= -PolyFn.eval (areaPoly Q r a) p := by
  have hcp : 0 ≤ coefficient Q r a*Real.pi := mul_nonneg hc Real.pi_pos.le
  simp only [area,areaPoly,PolyFn.eval,List.foldl,AffinePiece.eval,Fin.sum_univ_two,physicalArea]
  rcases le_total (((weights Q r a).S:ℝ)-((weights Q r a).L*p 0+(weights Q r a).L*p 1)) 0 with h | h
  · rw [max_eq_right h,max_eq_right (by nlinarith)];ring
  · rw [max_eq_left h,max_eq_left (by nlinarith)];ring

#check_explicit rawModel
#check_explicit maps
end SymplecticPacking.BranchLarge3.NativeInner
