import SymplecticPacking.HighDim.Handle.QuadricChartMargins
import SymplecticPacking.HighDim.Handle.RawFinitePartition
import OAI.Geometry.BallPacking.Surfaces.QuadricCurveManifold

/-!
# Formula coordinate boxes on the diagonal quadric

Formula coordinate boxes on the diagonal quadric subtype.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold

theorem realProd_closedBall_to_complex {z w : Plane} {r : ℝ}
    (hz : z ∈ Metric.closedBall w r) :
    Complex.equivRealProdCLM.symm z ∈ Metric.closedBall (Complex.equivRealProdCLM.symm w) (2*r) := by
  have hh : max |z.1-w.1| |z.2-w.2| ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def, Prod.fst_sub,
      Prod.snd_sub, Real.norm_eq_abs] using hz
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hbound := Complex.norm_le_abs_re_add_abs_im
    (Complex.equivRealProdCLM.symm z-Complex.equivRealProdCLM.symm w)
  change ‖Complex.equivRealProdCLM.symm z-Complex.equivRealProdCLM.symm w‖ ≤ 2*r
  change ‖Complex.equivRealProdCLM.symm z-Complex.equivRealProdCLM.symm w‖ ≤
    |z.1-w.1|+|z.2-w.2| at hbound
  have hh' := max_le_iff.mp hh
  exact hbound.trans (by linarith [hh'.1, hh'.2])

def ordinaryRealExplicitChart {m : ℕ} {a : Fin m → ℂ} (c : locus a)
    (hc : ∀ j, c.val.2 j ≠ 0) : OpenPartialHomeomorph (locus a) Plane :=
  (ordinaryExplicitChart c hc).trans Complex.equivRealProdCLM.toHomeomorph.toOpenPartialHomeomorph

def branchRealExplicitChart {m : ℕ} {a : Fin m → ℂ} (c : locus a) (i : Fin m)
    (hc : c.val ∈ regularCoordinate (some i)) : OpenPartialHomeomorph (locus a) Plane :=
  (branchExplicitChart c i hc).trans Complex.equivRealProdCLM.toHomeomorph.toOpenPartialHomeomorph

/-- A rational radius is accepted by finitely many strict root-distance inequalities. -/
def ordinaryRawBox {m : ℕ} {a : Fin m → ℂ} (c : locus a)
    (hc : ∀ j, c.val.2 j ≠ 0) (r : ℝ) (hr : 0 < r)
    (hmargin : ∀ j, (2*r)*(2*‖c.val.1‖+2*r) < ‖c.val.2 j‖^2) :
    RawCoordinateBox (locus a) where
  chart := ordinaryRealExplicitChart c hc
  point := Complex.equivRealProdCLM c.val.1
  radius := r
  radius_pos := hr
  closed_subset := by
    intro z hz
    refine ⟨Set.mem_univ _, ?_⟩
    apply ordinaryLocalTarget_closedBall c hc hmargin
    change Complex.equivRealProdCLM.symm z ∈ Metric.closedBall _ (2*r)
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using realProd_closedBall_to_complex hz

def branchRawBox {m : ℕ} {a : Fin m → ℂ} (c : locus a) (i : Fin m)
    (hc : c.val ∈ regularCoordinate (some i)) (r : ℝ) (hr : 0 < r)
    (hmargin₀ : (2*r)*(2*‖c.val.2 i‖+2*r) < ‖c.val.1‖^2)
    (hmargin : ∀ j, j≠i → (2*r)*(2*‖c.val.2 i‖+2*r) < ‖c.val.2 j‖^2) :
    RawCoordinateBox (locus a) where
  chart := branchRealExplicitChart c i hc
  point := Complex.equivRealProdCLM (c.val.2 i)
  radius := r
  radius_pos := hr
  closed_subset := by
    intro z hz
    refine ⟨Set.mem_univ _, ?_⟩
    apply branchLocalTarget_closedBall c i hc hmargin₀ hmargin
    change Complex.equivRealProdCLM.symm z ∈ Metric.closedBall _ (2*r)
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using realProd_closedBall_to_complex hz

section Compatibility
variable {m : ℕ} {a : Fin m → ℂ} [Fact (Injective a)] [Fact (∀ j, a j ≠ 0)]

theorem ordinaryRealExplicitChart_smooth (c : locus a) (hc : ∀ j, c.val.2 j ≠ 0) :
    ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ (ordinaryRealExplicitChart c hc) := by
  exact Complex.equivRealProdCLM.contDiff.contMDiff.comp
    (((curveCoordinate none).contDiff.restrict_scalars ℝ).contMDiff.comp (real_inclusion_contMDiff a))

theorem branchRealExplicitChart_smooth (c : locus a) (i : Fin m)
    (hc : c.val ∈ regularCoordinate (some i)) :
    ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ (branchRealExplicitChart c i hc) := by
  exact Complex.equivRealProdCLM.contDiff.contMDiff.comp
    (((curveCoordinate (some i)).contDiff.restrict_scalars ℝ).contMDiff.comp (real_inclusion_contMDiff a))

theorem ordinaryRealExplicitChart_inverse_smooth (c : locus a) (hc : ∀ j, c.val.2 j ≠ 0) :
    ContMDiffOn 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ (ordinaryRealExplicitChart c hc).symm
      (ordinaryRealExplicitChart c hc).target := by
  have hs := ((ordinaryLocalLift_smooth c hc).restrict_scalars ℝ).comp
    Complex.equivRealProdCLM.symm.contDiff.contDiffOn
    (show MapsTo Complex.equivRealProdCLM.symm (ordinaryRealExplicitChart c hc).target
      (ordinaryLocalTarget c) from fun _ hz => hz.2)
  intro z hz
  exact real_contMDiffWithinAt_of_ambient a (hs z hz)

theorem branchRealExplicitChart_inverse_smooth (c : locus a) (i : Fin m)
    (hc : c.val ∈ regularCoordinate (some i)) :
    ContMDiffOn 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ (branchRealExplicitChart c i hc).symm
      (branchRealExplicitChart c i hc).target := by
  have hs := ((branchLocalLift_smooth c i hc).restrict_scalars ℝ).comp
    Complex.equivRealProdCLM.symm.contDiff.contDiffOn
    (show MapsTo Complex.equivRealProdCLM.symm (branchRealExplicitChart c i hc).target
      (branchLocalTarget c i) from fun _ hz => hz.2)
  intro z hz
  exact real_contMDiffWithinAt_of_ambient a (hs z hz)

theorem ordinaryRawBox_smooth (c : locus a) (hc : ∀ j, c.val.2 j ≠ 0) (r : ℝ) (hr : 0 < r)
    (hmargin : ∀ j, (2*r)*(2*‖c.val.1‖+2*r) < ‖c.val.2 j‖^2) :
    (ordinaryRawBox c hc r hr hmargin).Smooth :=
  ⟨(ordinaryRealExplicitChart_smooth c hc).contMDiffOn,
    ordinaryRealExplicitChart_inverse_smooth c hc⟩

end Compatibility

#check_explicit ordinaryRawBox
#check_explicit branchRawBox
end SymplecticPacking.HighDim.ToricPackingStages
