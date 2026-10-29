import SymplecticPacking.BranchLarge3.Bridge
import OAI.Geometry.BallPacking.Main

/-!
# Necessity of the packing inequalities

From one real symplectic embedding to the existing Siegel--Yao rigidity theorem.
-/

noncomputable section
namespace SymplecticPacking.General
open Set Problem
open scoped ContDiff Topology

/-- Restriction and conjugation by the explicit real/complex phase equivalence
turn a single embedding of the original translated balls into the vendored
closed-source packing predicate. All maps are supplied by the premise. -/
theorem hasPacking_of_symplectic_embedding {n k : ℕ} {C : ℝ}
    {c : Fin k → ℝ} {s : Fin k → E n} (hdis : BallsDisjoint n k c s)
    {U : Set (E n)} (hU : IsOpen U) {F : E n → E n}
    (hsmooth : ContDiffOn ℝ ∞ F U)
    (hemb : Topology.IsEmbedding (fun x : U => F x))
    (hsymp : ∀ x ∈ U, IsSymplecticLinear (fderiv ℝ F x))
    (hsource : ∀ i, capBall (s i) (c i) ⊆ U)
    (hinto : ∀ i, MapsTo F (capBall (s i) (c i)) (capBallOpen 0 C)) :
    OAI.HigherDimensionalBallPacking.HasPacking n k C c := by
  letI : ContinuousSMul ℝ (E n) := IsBoundedSMul.continuousSMul
  let P := BranchLarge3.phaseEquiv n
  let L : E n →L[ℝ] (Fin n → ℂ) := P.toContinuousLinearMap
  let Q : (Fin n → ℂ) →L[ℝ] E n := P.symm.toContinuousLinearMap
  have hQP : ∀ z, toPhase (Q z)=z := fun z => BranchLarge3.toPhase_ofPhase z
  let g : Fin k → (Fin n → ℂ) → E n := fun i z => s i+Q z
  let V : Fin k → Set (Fin n → ℂ) := fun i => g i ⁻¹' U
  let f : Fin k → (Fin n → ℂ) → (Fin n → ℂ) := fun i z => L (F (g i z))
  have hgsm : ∀ i, ContDiff ℝ ∞ (g i) := fun i => contDiff_const.add Q.contDiff
  have hgc : ∀ i, Topology.IsEmbedding (g i) := by
    intro i
    exact (Homeomorph.addLeft (s i)).isEmbedding.comp P.symm.toHomeomorph.isEmbedding
  have hball : ∀ i z, z ∈ OAI.HigherDimensionalBallPacking.closedBall n (c i) →
      g i z ∈ capBall (s i) (c i) := by
    intro i z hz
    have hcap := BranchLarge3.capacity_toPhase (Q z)
    have hphase : toPhase (Q z)=z := BranchLarge3.toPhase_ofPhase z
    rw [hphase] at hcap
    change OAI.PackingSufficiencySupport.capacity z ≤ c i at hz
    change Real.pi*‖s i+Q z-s i‖^2 ≤ c i
    rw [add_sub_cancel_left,←hcap]
    exact hz
  have hIntoU : ∀ i z, z ∈ OAI.HigherDimensionalBallPacking.closedBall n (c i) → g i z ∈ U :=
    fun i z hz => hsource i (hball i z hz)
  refine ⟨V,f,?_,?_⟩
  · intro i
    refine ⟨fun z hz => hIntoU i z hz,?_,?_⟩
    · refine ⟨hU.preimage (hgsm i).continuous,?_,?_,?_⟩
      · exact L.contDiff.comp_contDiffOn (hsmooth.comp (hgsm i).contDiffOn (fun _ hx => hx))
      · have hgr : Topology.IsEmbedding (fun z : V i => g i z) :=
          (hgc i).comp Topology.IsEmbedding.subtypeVal
        have hcod := hgr.codRestrict U (fun z : V i => z.property)
        exact P.toHomeomorph.isEmbedding.comp (hemb.comp hcod)
      · intro z hz u v
        have hdQ : HasFDerivAt (g i) Q z := by
          change HasFDerivAt (fun w => s i+Q w) Q z
          exact Q.hasFDerivAt.const_add (s i)
        have hdF : HasFDerivAt F (fderiv ℝ F (g i z)) (g i z) :=
          (hsmooth.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp) |>.hasFDerivAt
        have hdL : HasFDerivAt (fun x => L x) L (F (g i z)) := L.hasFDerivAt
        have hdf : HasFDerivAt (f i) (L.comp ((fderiv ℝ F (g i z)).comp Q)) z := by
          simpa only [f,Function.comp_def] using hdL.comp z (hdF.comp z hdQ)
        rw [hdf.fderiv]
        change OAI.PackingSufficiencySupport.standardForm
          (toPhase (fderiv ℝ F (g i z) (Q u))) (toPhase (fderiv ℝ F (g i z) (Q v))) =
            OAI.PackingSufficiencySupport.standardForm u v
        rw [BranchLarge3.standardForm_toPhase]
        calc
          _ = Problem.omega0 (Q u) (Q v) := hsymp (g i z) hz (Q u) (Q v)
          _ = OAI.PackingSufficiencySupport.standardForm (toPhase (Q u)) (toPhase (Q v)) :=
            (BranchLarge3.standardForm_toPhase (Q u) (Q v)).symm
          _ = _ := by rw [hQP,hQP]
    · intro z hz
      have hh := hinto i (hball i z hz)
      have hcap := BranchLarge3.capacity_toPhase (F (g i z))
      change Real.pi*‖F (g i z)-0‖^2 < C at hh
      rw [sub_zero] at hh
      change OAI.PackingSufficiencySupport.capacity (toPhase (F (g i z))) < C
      rw [hcap]
      exact hh
  · intro i j hij
    apply Set.disjoint_left.mpr
    rintro z ⟨a,ha,rfl⟩ ⟨b,hb,heq⟩
    have hF : F (g j b)=F (g i a) := P.injective heq
    have hxy : (⟨g j b,hIntoU j b hb⟩ : U)=⟨g i a,hIntoU i a ha⟩ := hemb.injective hF
    have hv : g j b=g i a := congrArg Subtype.val hxy
    exact Set.disjoint_left.mp (hdis i j hij) (hball i a ha) (hv ▸ hball j b hb)

/-- The necessary volume and pair inequalities for the paper's single-embedding
formulation. The rigidity inputs are the vendored volume and two-ball obstructions; the
vendored sufficiency theorem is not used. -/
theorem symplectic_embedding_necessary {n k : ℕ} (hn : 3 ≤ n) (hk : 1 ≤ k)
    {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n} (hC : 0 < C) (hc : ∀ i, 0 < c i)
    (hdis : BallsDisjoint n k c s) {U : Set (E n)} (hU : IsOpen U) {F : E n → E n}
    (hsmooth : ContDiffOn ℝ ∞ F U) (hemb : Topology.IsEmbedding (fun x : U => F x))
    (hsymp : ∀ x ∈ U, IsSymplecticLinear (fderiv ℝ F x))
    (hsource : ∀ i, capBall (s i) (c i) ⊆ U)
    (hinto : ∀ i, MapsTo F (capBall (s i) (c i)) (capBallOpen 0 C)) :
    (∑ i, c i^n) < C^n ∧ ∀ i j, i ≠ j → c i+c j < C := by
  have hp := hasPacking_of_symplectic_embedding hdis hU hsmooth hemb hsymp hsource hinto
  exact ⟨hp.volume_lt (by omega) hC hc, hp.strict_pair_bound hn hC hc⟩

end SymplecticPacking.General
