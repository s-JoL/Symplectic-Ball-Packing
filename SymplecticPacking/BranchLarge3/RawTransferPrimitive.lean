import SymplecticPacking.BranchLarge3.CubicBridge
import SymplecticPacking.BranchLarge3.CubicFamily
import SymplecticPacking.BranchLarge3.CubicRawForms
import SymplecticPacking.HighDim.Handle.RawFullProductMoserSpec

/-!
# Ambient representatives of the cubic degeneration primitive

Ambient-coordinate representatives of the compact cubic degeneration primitive.
-/

noncomputable section
namespace SymplecticPacking.BranchLarge3.RawTransfer

open Set Function Manifold
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.FiniteMoment
open OAI.PackingSufficiencySupport.FiniteMoment.Radial
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology

abbrev Ambient := Affine 2 × PlanePhase (Fin 2)

/-- The bridge formula evaluated before restriction to the affine quadric. -/
def bridge (A B D S : ℕ) (L δ : ℝ) (p : Ambient) : Affine 2 × DiskPair :=
  (p.1, CubicBridge.fibre A B δ
    (RawCubic.coefficientMap A B D S p.1, physicalDiskCoordinates L p.2))

theorem bridge_contDiff {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    (D S : ℕ) (L : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (bridge A B D S L δ) := by
  have ha : ContDiff ℝ ∞ (fun p : Ambient =>
      (RawCubic.coefficientMap A B D S p.1,physicalDiskCoordinates L p.2)) :=
    ((RawCubic.coefficientMap_contDiff A B D S).comp contDiff_fst).prodMk
      ((physicalDiskCoordinates L).contDiff.comp contDiff_snd)
  apply contDiff_fst.prodMk
  apply contDiff_iff_contDiffAt.mpr
  intro p
  exact (CubicBridge.fibre_contDiffAt hA hAB hδ
    (fun i => lt_of_lt_of_le zero_lt_one (RawCubic.coefficient_ge_one _ _ _))).comp p ha.contDiffAt

theorem bridge_restrict (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace)
    (p : CubicPhysicalSpace) :
    bridge A B D S L (CubicBridge.delta A B L K) (p.1.val,p.2) =
      ((bridgeMap A B D S L K p).1.val,(bridgeMap A B D S L K p).2) := by
  have he : RawCubic.coefficientMap A B D S p.1 = CubicBridge.weights A B D S p.1 := by
    funext i
    simp only [CubicBridge.weights,cubicCoefficients_squares]
    rfl
  simp only [bridge,bridgeMap,he]

/-- The full ambient degeneration map. Its derivative includes the vertical dependence
of the normal-lift flow and of the radial bridge. -/
def coneMap (A B D S : ℕ) (L δ : ℝ) (KB : Set BaseCurve) (KH : Set DiskPair)
    (p : ℝ × Ambient) : CubicConeTarget :=
  let q := bridge A B D S L δ p.2
  ((CubicFamily.flowY (CubicFamily.mPar KB) (CubicFamily.RPar KB KH)
    p.1 (projection q.1,q.2.2)).1,q.2)

theorem coneMap_contDiff {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    (D S : ℕ) (L : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (KB : Set BaseCurve) (KH : Set DiskPair) :
    ContDiff ℝ ∞ (coneMap A B D S L δ KB KH) := by
  have hb := (bridge_contDiff hA hAB D S L hδ).comp (contDiff_snd :
    ContDiff ℝ ∞ (Prod.snd : ℝ × Ambient → Ambient))
  have hy : ContDiff ℝ ∞ (fun p : ℝ × Ambient =>
      (projection (bridge A B D S L δ p.2).1,(bridge A B D S L δ p.2).2.2)) :=
    ((projection_contDiff.restrict_scalars ℝ).comp hb.fst).prodMk hb.snd.snd
  have hf := (CubicFamily.tfield_csField (CubicFamily.mPar_pos KB)
    (CubicFamily.RPar KB KH)).flow_smooth
  exact ((hf.comp (contDiff_fst.prodMk hy)).fst).prodMk hb.snd

/-- A native covector on the ambient affine space, restricted only in its evaluation
point. No manifold derivative is read by this definition. -/
def ambientCovector (A B D S : ℕ) (c L δ : ℝ) (KB : Set BaseCurve) (KH : Set DiskPair)
    (p : ℝ × Ambient) : Ambient →L[ℝ] ℝ :=
  (cubicConePrimitive (A := A) (B := B) D S c (coneMap A B D S L δ KB KH p)).comp
    (fderiv ℝ (fun y => coneMap A B D S L δ KB KH (p.1,y)) p.2)

theorem ambientCovector_contDiff {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    (D S : ℕ) (c L : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (KB : Set BaseCurve) (KH : Set DiskPair) :
    ContDiff ℝ ∞ (ambientCovector A B D S c L δ KB KH) := by
  have hg := coneMap_contDiff hA hAB D S L hδ KB KH
  have harg : ContDiff ℝ ∞ (fun p : (ℝ × Ambient) × Ambient => (p.1.1,p.2)) :=
    contDiff_fst.fst.prodMk contDiff_snd
  have hd : ContDiff ℝ ∞ (fun p : ℝ × Ambient =>
      fderiv ℝ (fun y => coneMap A B D S L δ KB KH (p.1,y)) p.2) :=
    (hg.comp harg).fderiv contDiff_snd (by simp)
  exact ((cubicConePrimitive_smooth D S c).comp hg).clm_comp hd

def covector (A B D S : ℕ) (c L δ : ℝ) (KB : Set BaseCurve) (KH : Set DiskPair)
    (t : ℝ) (p : CubicPhysicalSpace) : Ambient →L[ℝ] ℝ :=
  ambientCovector A B D S c L δ KB KH (t,(p.1.val,p.2))

theorem coneMap_restrict (A B D S : ℕ) (c L : ℝ) (K : Set CubicPhysicalSpace)
    (KB : Set BaseCurve) (KH : Set DiskPair) (t : ℝ) (p : CubicPhysicalSpace) :
    coneMap A B D S L (CubicBridge.delta A B L K) KB KH (t,(p.1.val,p.2)) =
      ((famMap A B D S c KB KH (t,bridgeMap A B D S L K p)).1,
        (bridgeMap A B D S L K p).2) := by
  unfold coneMap
  rw [bridge_restrict]
  rfl

theorem product_inclusion_contMDiff :
    ContMDiff 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,Ambient) ∞
      (fun p : CubicPhysicalSpace => (p.1.val,p.2)) := by
  have hid : ContMDiff 𝓘(ℝ,PlanePhase (Fin 2)) 𝓘(ℝ,PlanePhase (Fin 2)) ∞
      (id : PlanePhase (Fin 2) → PlanePhase (Fin 2)) := contMDiff_id
  have h := (real_inclusion_contMDiff (parameters 0)).prodMap
    hid
  simp +instances only [← modelWithCornersSelf_prod,chartedSpaceSelf_prod] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem product_inclusion_mfderiv (p : CubicPhysicalSpace) :
    mfderiv 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,Ambient)
      (fun q : CubicPhysicalSpace => (q.1.val,q.2)) p =
    (mfderiv 𝓘(ℝ,RealModel) 𝓘(ℝ,Affine 2) (Subtype.val : BaseCurve → Affine 2) p.1).prodMap
      (ContinuousLinearMap.id ℝ (PlanePhase (Fin 2))) := by
  rw [modelWithCornersSelf_prod,modelWithCornersSelf_prod,←chartedSpaceSelf_prod]
  exact (mfderiv_prodMap
    ((real_inclusion_contMDiff (parameters 0)).mdifferentiable (by simp) p.1)
    (mdifferentiableAt_id (I:=𝓘(ℝ,PlanePhase (Fin 2))) (x:=p.2))).trans (by
      rw [mfderiv_id]
      rfl)

theorem pullback_oneForm_comp
    {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {M N P : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
    [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
    [TopologicalSpace P] [ChartedSpace G P] [IsManifold 𝓘(ℝ,G) ∞ P]
    (α : ℝ → ManifoldOneForm G P) {f : M → N} {g : N → P}
    (hf : ContMDiff 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f) (hg : ContMDiff 𝓘(ℝ,F) 𝓘(ℝ,G) ∞ g)
    (t : ℝ) :
    manifoldPullbackOneForm (E:=G) (F:=E) α (g ∘ f) t =
      manifoldPullbackOneForm (E:=F) (F:=E)
        (manifoldPullbackOneForm (E:=G) (F:=F) α g) f t := by
  funext x
  have hd := manifoldMapDifferential_comp (hg.mdifferentiable (by simp) (f x))
    (hf.mdifferentiable (by simp) x)
  simp only [manifoldPullbackOneForm,Function.comp_apply,hd,ContinuousLinearMap.comp_assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem native_pullback_semantic
    {E V F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M : Type} [TopologicalSpace M] [ChartedSpace Hamiltonian.Plane M]
    [IsManifold 𝓘(ℝ,Hamiltonian.Plane) ∞ M]
    (ι : M → E) (g : E × V → F) (β : F → F →L[ℝ] ℝ)
    (hinc : ContMDiff 𝓘(ℝ,Hamiltonian.Plane × V) 𝓘(ℝ,E × V) ∞
      (fun x : M × V => (ι x.1,x.2)))
    (hdinc : ∀ x : M × V,
      mfderiv 𝓘(ℝ,Hamiltonian.Plane × V) 𝓘(ℝ,E × V) (fun x : M × V => (ι x.1,x.2)) x =
        (mfderiv 𝓘(ℝ,Hamiltonian.Plane) 𝓘(ℝ,E) ι x.1).prodMap (ContinuousLinearMap.id ℝ V))
    (hg : ContDiff ℝ ∞ g) :
    HighDim.ToricPackingStages.semanticFullOneForm ι
      (fun x : M × V => (β (g (ι x.1,x.2))).comp (fderiv ℝ g (ι x.1,x.2))) =
    manifoldPullbackOneForm (E:=F) (F:=Hamiltonian.Plane × V)
      (fun _ => β) (fun x : M × V => g (ι x.1,x.2)) 0 := by
  funext x
  have hd := mfderiv_comp x (hg.contMDiff.mdifferentiable (by simp) (ι x.1,x.2))
    (hinc.mdifferentiable (by simp) x)
  rw [mfderiv_eq_fderiv,hdinc] at hd
  apply ContinuousLinearMap.ext
  intro u
  exact congrArg (β (g (ι x.1,x.2))) (congrArg (fun f : (Hamiltonian.Plane × V) →L[ℝ] F => f u) hd.symm)

theorem covector_semantic {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    (D S : ℕ) (c L : ℝ) (K : Set CubicPhysicalSpace)
    (hδ : 0 < CubicBridge.delta A B L K) (KB : Set BaseCurve) (KH : Set DiskPair)
    (hΞ : ContMDiff 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicConeModel) ∞ (bridgeMap A B D S L K))
    (t : ℝ)
    (hg : ContMDiff 𝓘(ℝ,CubicConeModel) 𝓘(ℝ,CubicConeTarget) ∞
      (fun q : CubicConeSpace => ((famMap A B D S c KB KH (t,q)).1,q.2))) :
    HighDim.ToricPackingStages.semanticFullOneForm
      (Subtype.val : BaseCurve → Affine 2)
      (covector A B D S c L (CubicBridge.delta A B L K) KB KH t) =
    manifoldPullbackOneForm (famPrim A B D S c KB KH) (bridgeMap A B D S L K) t := by
  let raw := fun z : Ambient => coneMap A B D S L (CubicBridge.delta A B L K) KB KH (t,z)
  let inc := fun q : CubicPhysicalSpace => (q.1.val,q.2)
  let g := fun q : CubicConeSpace => ((famMap A B D S c KB KH (t,q)).1,q.2)
  have hr : ContDiff ℝ ∞ raw := (coneMap_contDiff hA hAB D S L hδ KB KH).comp
    (contDiff_const.prodMk contDiff_id)
  have he : raw ∘ inc = g ∘ bridgeMap A B D S L K :=
    funext (coneMap_restrict A B D S c L K KB KH t)
  have hn := native_pullback_semantic (Subtype.val : BaseCurve → Affine 2) raw
    (cubicConePrimitive (A:=A) (B:=B) D S c) product_inclusion_contMDiff
    product_inclusion_mfderiv hr
  change HighDim.ToricPackingStages.semanticFullOneForm (Subtype.val : BaseCurve → Affine 2)
      (covector A B D S c L (CubicBridge.delta A B L K) KB KH t) =
    manifoldPullbackOneForm (fun _ => cubicConePrimitive (A:=A) (B:=B) D S c) (raw ∘ inc) 0 at hn
  rw [he,pullback_oneForm_comp _ hΞ hg] at hn
  exact hn

#check_explicit bridge
#check_explicit coneMap
#check_explicit ambientCovector
#check_explicit covector

end SymplecticPacking.BranchLarge3.RawTransfer
