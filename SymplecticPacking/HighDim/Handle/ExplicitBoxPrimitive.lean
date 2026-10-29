import SymplecticPacking.HighDim.Handle.ExplicitLineBump

/-!
# Explicit primitives on coordinate boxes

Fixed coordinate-integral primitives using the displayed transition bump.

Coordinate-integral proof adapted from `vendor/OAI/Geometry/BallPacking/SurfaceArea/QuadricEndAnnuli.lean`.
Original source: OpenAI, Apache-2.0; see vendor/LICENSE and vendor/NOTICE.
The formulas here use fixed transition functions in place of existential bump data.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold MeasureTheory
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology

def formulaFixedCovectorOperator (A : ℝ) (hA : 0<A) (f : Plane → ℝ) (z : Plane) : Plane →L[ℝ] ℝ :=
  planarCovector (planarPrimitiveX A f (formulaLineBump A) z)
    (planarPrimitiveY A f (formulaLineBump A) z)

theorem formulaFixedCovectorOperator_spec {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {A : ℝ} (hA : 0<A)
    {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ p x y, A ≤ |x| ∨ A ≤ |y| → f (p,(x,y))=0)
    (hmass : ∀ p, (∫ x, f (p,x))=0) :
    ContDiff ℝ ∞ (fun q : P × Plane => formulaFixedCovectorOperator A hA (fun x => f (q.1,x)) q.2) ∧
      (∀ p x y, A ≤ |x| ∨ A ≤ |y| → formulaFixedCovectorOperator A hA (fun z => f (p,z)) (x,y)=0) ∧
      (∀ p z, euclideanExteriorOneForm (formulaFixedCovectorOperator A hA (fun x => f (p,x))) z =
        f (p,z) • planarArea) := by
  let ρ := formulaLineBump A
  obtain ⟨hρ, _, _, hρs, hρmass⟩ := formulaLineBump_spec hA
  have hρ1 : (∫ x in -A..A, ρ x) = 1 := by
    rw [integral_eq_full_of_box_support hρs]
    exact hρmass
  have hfy (y : P) : ContDiff ℝ ∞ (fun x => f (y,x)) :=
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hfc (y : P) : HasCompactSupport (fun x => f (y,x)) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0:Plane) A)
    intro p hp
    have hh : A < max |p.1| |p.2| := by
      simpa only [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,Real.norm_eq_abs,not_le] using hp
    exact hzero y p.1 p.2 ((lt_max_iff.mp hh).imp le_of_lt le_of_lt)
  have hg (y : P) : ContDiff ℝ ∞ (planarMarginal A (fun x => f (y,x))) :=
    planarMarginal_smooth (hfy y) A
  have hgt (y : P) (t : ℝ) (ht : A ≤ |t|) : planarMarginal A (fun x => f (y,x)) t=0 := by
    unfold planarMarginal
    have he : (fun x => f (y,(x,t))) = fun _ => (0:ℝ) := funext fun x => hzero y x t (Or.inr ht)
    rw [he,intervalIntegral.integral_zero]
  have hgm (y : P) (t : ℝ) : planarMarginal A (fun x => f (y,x)) t = ∫ x, f (y,(x,t)) :=
    integral_eq_full_of_box_support (fun x hx => hzero y x t (Or.inl hx))
  have hgm0 (y : P) : (∫ t in -A..A, planarMarginal A (fun x => f (y,x)) t)=0 := by
    rw [integral_eq_full_of_box_support (hgt y)]
    simp_rw [hgm]
    rw [←integral_prod_symm (fun x => f (y,x))]
    · exact hmass y
    · exact (hfy y).continuous.integrable_of_hasCompactSupport (hfc y)
  let U : P × Plane → ℝ := fun p => planarPrimitiveX A (fun x => f (p.1,x)) ρ p.2
  let V : P × Plane → ℝ := fun p => planarPrimitiveY A (fun x => f (p.1,x)) ρ p.2
  have hU : ContDiff ℝ ∞ U := (planarPrimitive_parameter_smooth hf hρ A).1
  have hV : ContDiff ℝ ∞ V := (planarPrimitive_parameter_smooth hf hρ A).2
  change ContDiff ℝ ∞ (fun q => planarCovector (U q) (V q)) ∧
    (∀ p x y, A ≤ |x| ∨ A ≤ |y| → planarCovector (U (p,(x,y))) (V (p,(x,y)))=0) ∧
    (∀ p z, euclideanExteriorOneForm (fun x => planarCovector (U (p,x)) (V (p,x))) z = f (p,z) • planarArea)
  refine ⟨planarCovector_smooth hU hV,?_,?_⟩
  · intro p x y h
    obtain ⟨h1,h2⟩ := planarPrimitive_zero_outside hA.le (hfy p).continuous hρ.continuous
      (hzero p) hρs hρ1 (hg p).continuous (hgm0 p) (x,y) h
    change planarCovector (planarPrimitiveX A (fun z => f (p,z)) ρ (x,y))
      (planarPrimitiveY A (fun z => f (p,z)) ρ (x,y))=0
    rw [h1,h2,planarCovector_zero]
  · intro p z
    have hUp : ContDiff ℝ ∞ (fun x => U (p,x)) := hU.comp (contDiff_const.prodMk contDiff_id)
    have hVp : ContDiff ℝ ∞ (fun x => V (p,x)) := hV.comp (contDiff_const.prodMk contDiff_id)
    rw [planarCovector_exterior hUp hVp]
    congr 1
    exact planarPrimitive_curl (hfy p).continuous hρ.continuous (hg p).continuous z

def formulaTranslatedCovectorOperator (A : ℝ) (hA : 0<A) (a : Plane) (f : Plane → ℝ) (z : Plane) : Plane →L[ℝ] ℝ :=
  formulaFixedCovectorOperator A hA (fun w => f (w+a)) (z-a)

theorem formulaTranslatedCovectorOperator_spec {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {A : ℝ} (hA : 0<A) (a : Plane)
    {f : P × Plane → ℝ} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ p x y, A ≤ |x-a.1| ∨ A ≤ |y-a.2| → f (p,(x,y))=0)
    (hmass : ∀ p, (∫ x, f (p,x))=0) :
    ContDiff ℝ ∞ (fun q : P × Plane => formulaTranslatedCovectorOperator A hA a (fun x => f (q.1,x)) q.2) ∧
      (∀ p x y, A ≤ |x-a.1| ∨ A ≤ |y-a.2| → formulaTranslatedCovectorOperator A hA a (fun z => f (p,z)) (x,y)=0) ∧
      (∀ p z, euclideanExteriorOneForm (formulaTranslatedCovectorOperator A hA a (fun x => f (p,x))) z =
        f (p,z) • planarArea) := by
  let g : P × Plane → ℝ := fun q => f (q.1,q.2+a)
  have hg : ContDiff ℝ ∞ g := hf.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))
  have hgzero : ∀ p x y, A ≤ |x| ∨ A ≤ |y| → g (p,(x,y))=0 := by
    intro p x y h
    apply hzero
    simpa only [add_sub_cancel_right] using h
  have hgmass : ∀ p, (∫ x, g (p,x))=0 := by
    intro p
    exact (integral_add_right_eq_self (fun x => f (p,x)) a).trans (hmass p)
  have hs := formulaFixedCovectorOperator_spec (P := P) (A := A) hA (f := g) hg hgzero hgmass
  refine ⟨?_,?_,?_⟩
  · have hh : ContDiff ℝ ∞ (fun q : P × Plane =>
        formulaFixedCovectorOperator A hA (fun w => g (q.1,w)) (q.2-a)) :=
      translated_covector_family_smooth (β := fun q : P × Plane =>
        formulaFixedCovectorOperator A hA (fun w => g (q.1,w)) q.2) hs.1 a
    exact hh
  · intro p x y h
    exact hs.2.1 p (x-a.1) (y-a.2) h
  · intro p z
    have hβp : ContDiff ℝ ∞ (formulaFixedCovectorOperator A hA (fun x => g (p,x))) :=
      covector_family_slice_smooth (β := fun q : P × Plane =>
        formulaFixedCovectorOperator A hA (fun w => g (q.1,w)) q.2) hs.1 p
    change euclideanExteriorOneForm (fun x => formulaFixedCovectorOperator A hA (fun w => g (p,w)) (x-a)) z = _
    rw [translated_covector_exterior (a := a) (z := z) hβp,hs.2.2]
    simp only [g,sub_add_cancel]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

end SymplecticPacking.HighDim.ToricPackingStages
