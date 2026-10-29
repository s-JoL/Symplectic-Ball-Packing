import SymplecticPacking.HighDim.Handle.QuadricRawPresentationGeometry
import SymplecticPacking.HighDim.Handle.QuadricBoxCode

/-!
# Global cover of the quadric surface by formula raw charts

Formula raw charts provide every tangent coordinate needed by the semantic proof bridge.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
variable {m : ℕ} (a : Fin m → ℂ)
  [Fact (Injective a)] [Fact (∀ j,a j≠0)]

def quadricCodeRootChart (code : QuadricBoxCode m) (h : QuadricBoxCode.Valid a code) : QuadricRootChart a :=
  match code,h with
  | .ordinary q ε r,h =>
    ⟨ordinaryPresentationCenter a ε (rationalComplex q),none,
      QuadricBoxCode.ordinary_margin_regular a h.1 h.2⟩
  | .branch i ε₀ ε r,h =>
    ⟨branchPresentationCenter a i ε₀ ε,some i,
      branchPresentationCenter_regular a Fact.out Fact.out i ε₀ ε⟩

theorem quadricCodeRootChart_chart (code : QuadricBoxCode m) (h : QuadricBoxCode.Valid a code) :
    (QuadricBoxCode.box a code h).chart=(quadricCodeRootChart a code h).chart := by
  cases code <;> rfl

def quadricCodeAmbientBox (code : QuadricBoxCode m) (h : QuadricBoxCode.Valid a code) :
    RawAmbientBox (Affine m) (locus a) :=
  (quadricCodeRootChart a code h).ambientBox (QuadricBoxCode.box a code h) (quadricCodeRootChart_chart a code h)

theorem quadric_raw_global_cover (x : locus a) :
    ∃ C : RawAmbientBox (Affine m) (locus a),
      C.inclusion=Subtype.val ∧ C.box.Smooth ∧
      ContDiffOn ℝ ∞ C.inverseAmbient C.box.chart.target ∧ x ∈ C.box.chart.source := by
  obtain ⟨code,h,hin⟩ := QuadricBoxCode.code_cover a x
  refine ⟨quadricCodeAmbientBox a code h,rfl,?_,?_,hin.1⟩
  · exact (quadricCodeRootChart a code h).box_smooth _ (quadricCodeRootChart_chart a code h)
  · exact (quadricCodeRootChart a code h).ambientBox_inverse_smooth _ (quadricCodeRootChart_chart a code h)

#check_explicit quadricCodeAmbientBox
end SymplecticPacking.HighDim.ToricPackingStages
