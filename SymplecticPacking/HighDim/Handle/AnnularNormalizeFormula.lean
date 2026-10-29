import SymplecticPacking.HighDim.Handle.AnnularCutoff

/-!
# Explicit annular normalization formula

Explicit annular normalization: period correction and a fixed annular cutoff.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Manifold MeasureTheory Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.Hamiltonian.AnnularHandleData
open scoped ContDiff Manifold Topology

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M]

def annularDifference (D : AnnularHandleData Plane M)
    (Γ N : P → ManifoldOneForm Plane M) : P → ManifoldOneForm CylinderModel HandleCylinder :=
  parameterManifoldPullbackOneForm (fun p => Γ p-N p) D.chart

def annularPotential (D : AnnularHandleData Plane M) (Γ N : P → ManifoldOneForm Plane M) : P × M → ℝ :=
  annularCoordinatePotential 0 (annularDifference D Γ N) D.clock D.chart.symm

def annularNormalizeOf (D : AnnularHandleData Plane M) (b : ℝ)
    (Γ N : P → ManifoldOneForm Plane M) : P → ManifoldOneForm Plane M :=
  normalizedManifoldPrimitive Γ D.dual
    (cylinderFormPeriod 0 (annularDifference D Γ N))
    (fun q => annularCutoff D (annularCutWidth D b) q.2 * annularPotential D Γ N q)

/-- The displayed potential has the exact period-corrected differential. -/
theorem annularPotential_spec
    {V : Set P} {I : Set ℝ} (hV : IsOpen V) (hI : IsOpen I) (hc : Convex ℝ I)
    {a : ℝ} (ha : a ∈ I)
    (e : PartialDiffeomorph 𝓘(ℝ,CylinderModel) 𝓘(ℝ,Plane) HandleCylinder M ∞)
    (he_source : e.source = I ×ˢ univ)
    {Γ N : P → ManifoldOneForm Plane M} {β : ManifoldOneForm Plane M}
    (hΓ : ∀ c, ContDiffOn ℝ ∞ (fun q : P × Plane => chartOneForm (Γ q.1) c q.2)
      (V ×ˢ (extChartAt 𝓘(ℝ,Plane) c).target))
    (hN : ∀ p ∈ V, ∀ x ∈ e.target, ContDiffAt ℝ ∞
      (fun q : P × Plane => chartOneForm (N q.1) x q.2) (p,extChartAt 𝓘(ℝ,Plane) x x))
    (hcurv : ∀ p ∈ V, ∀ x ∈ e.target,
      manifoldExteriorOneForm (Γ p) x = manifoldExteriorOneForm (N p) x)
    {f : Circle → ℝ} (hf : ContMDiff 𝓘(ℝ,CircleModel) 𝓘(ℝ,ℝ) ∞ f)
    (hfint : (∫ t in (0:ℝ)..1, f (circleTurn t)) = 1)
    (hβcoord : ∀ z ∈ e.source, ∀ v : CylinderModel,
      β (e z) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,Plane) e z v) =
        f z.2 * circleAngular z.2 v.2) :
    let α := parameterManifoldPullbackOneForm (fun p => Γ p-N p) e;
    let F := annularCoordinatePotential a α f e.symm;
    ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ F (V ×ˢ e.target) ∧
      ContDiffOn ℝ ∞ (cylinderFormPeriod a α) V ∧
      ∀ p ∈ V, ∀ x ∈ e.target,
        manifoldScalarDifferential (E := Plane) (fun y => F (p,y)) x =
          Γ p x-N p x-cylinderFormPeriod a α p • β x := by
  let δ : P → ManifoldOneForm Plane M := fun p => Γ p-N p
  let α := parameterManifoldPullbackOneForm (E := Plane) (F := CylinderModel) δ e
  have hΓat (p : P) (hp : p∈V) (x : M) : ContDiffAt ℝ ∞
      (fun q : P × Plane => chartOneForm (Γ q.1) x q.2) (p,extChartAt 𝓘(ℝ,Plane) x x) :=
    (hΓ x).contDiffAt ((hV.prod (isOpen_extChartAt_target (I := 𝓘(ℝ,Plane)) x)).mem_nhds
      ⟨hp,(extChartAt 𝓘(ℝ,Plane) x).map_source (mem_extChartAt_source x)⟩)
  have hδ (p : P) (hp : p∈V) (x : M) (hx : x∈e.target) : ContDiffAt ℝ ∞
      (fun q : P × Plane => chartOneForm (δ q.1) x q.2) (p,extChartAt 𝓘(ℝ,Plane) x x) := by
    apply ((hΓat p hp x).sub (hN p hp x hx)).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun q => chartOneForm_sub (Γ q.1) (N q.1) x q.2)
  have hδclosed (p : P) (hp : p∈V) (x : M) (hx : x∈e.target) :
      manifoldExteriorOneForm (δ p) x=0 := by
    change manifoldExteriorOneForm (Γ p-N p) x=0
    rw [manifoldExteriorOneForm_sub_at (α := Γ p) (β := N p) (x := x)
      ((hΓat p hp x).comp _ (contDiffAt_const.prodMk contDiffAt_id))
      ((hN p hp x hx).comp _ (contDiffAt_const.prodMk contDiffAt_id)),hcurv p hp x hx]
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    change _-_ = (0:ℝ)
    ring
  have hsrc (z : HandleCylinder) (hz : z.1∈I) : z∈e.source := by
    rw [he_source]; exact ⟨hz,mem_univ _⟩
  have hα (p : P) (hp : p∈V) (z : HandleCylinder) (hz : z.1∈I) : ContDiffAt ℝ ∞
      (fun q : P × CylinderModel => chartOneForm (α q.1) z q.2)
      (p,extChartAt 𝓘(ℝ,CylinderModel) z z) :=
    parameterManifoldPullbackOneForm_contDiffAt (α := δ) (g := e)
      (hδ p hp (e z) (e.map_source (hsrc z hz))) (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (hsrc z hz)))
  have hclosed (p : P) (hp : p∈V) (z : HandleCylinder) (hz : z.1∈I) :
      manifoldExteriorOneForm (α p) z=0 := by
    change manifoldExteriorOneForm (manifoldPullbackOneForm (E := Plane) (F := CylinderModel) (fun _ => δ p) e 0) z=0
    rw [manifold_pullback_exterior_at (α := δ p) (g := e) (b := z)
      ((hδ p hp (e z) (e.map_source (hsrc z hz))).comp _ (contDiffAt_const.prodMk contDiffAt_id))
      (e.contMDiffOn.contMDiffAt (e.open_source.mem_nhds (hsrc z hz)))]
    dsimp only [manifoldPullbackTwoForm]
    rw [hδclosed p hp (e z) (e.map_source (hsrc z hz))]
    rfl
  have hmem (x : M) (hx : x∈e.target) : (e.symm x).1∈I := by
    have hm := e.map_target hx
    rw [he_source] at hm
    exact hm.1
  let F := annularCoordinatePotential a α f e.symm
  obtain ⟨hF,hFd⟩ := annularCoordinatePotential_spec hV hI e.open_target hc ha
    hα hclosed hf hfint e.symm.contMDiffOn hmem
  have hFd' : ∀ p∈V,∀ x∈e.target,
      manifoldScalarDifferential (E := Plane) (fun y => F (p,y)) x=
        Γ p x-N p x-cylinderFormPeriod a α p • β x := by
    intro p hp x hx
    apply ContinuousLinearMap.ext
    intro v
    rw [hFd p hp x hx v]
    have hd := parameterManifoldPullbackOneForm_inverse_apply e δ p hx v
    change α p (e.symm x) (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) e.symm x v)=_ at hd
    rw [hd]
    have hbc := hβcoord (e.symm x) (e.map_target hx)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) e.symm x v)
    have hb := parameterManifoldPullbackOneForm_inverse_apply e (fun _ : P => β) p hx v
    change β (e (e.symm x)) (mfderiv 𝓘(ℝ,CylinderModel) 𝓘(ℝ,Plane) e (e.symm x)
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,CylinderModel) e.symm x v))=β x v at hb
    rw [hb] at hbc
    simp only [δ,Pi.sub_apply,sub_apply,smul_apply,smul_eq_mul]
    rw [hbc]
    ring
  exact ⟨hF, cylinderFormPeriod_smooth hV ha hα, hFd'⟩

/-- An explicit open neighbourhood of the closed working band. -/
def annularNormalizeRegion (D : AnnularHandleData Plane M) (b : ℝ) : Set M :=
  D.chart.target ∩ (fun x => (D.chart.symm x).1) ⁻¹'
    Ioo (-annularCutWidth D b) (annularCutWidth D b)

theorem annularNormalizeRegion_open (D : AnnularHandleData Plane M) (b : ℝ) :
    IsOpen (annularNormalizeRegion D b) :=
  (annular_inverse_fst_smooth D.chart).continuousOn.isOpen_inter_preimage D.chart.open_target isOpen_Ioo

theorem annularNormalizeRegion_band (D : AnnularHandleData Plane M) {b : ℝ}
    (hbw : b < D.width) : D.chart '' band b ⊆ annularNormalizeRegion D b := by
  rintro x ⟨z, hz, rfl⟩
  have hzs := D.band_subset_source hbw hz
  refine ⟨D.chart.map_source hzs, ?_⟩
  have he : (D.chart.symm (D.chart z)).1 = z.1 := congrArg Prod.fst (D.chart.left_inv hzs)
  change (D.chart.symm (D.chart z)).1 ∈ Ioo _ _
  rw [he]
  constructor <;> dsimp [annularCutWidth] <;> linarith [hz.1.1, hz.1.2]

/-- Complete specification of the annular normalization formula. -/
theorem annularNormalizeOf_spec (D : AnnularHandleData Plane M) {b : ℝ} (hbw : b < D.width)
    {Γ N : P → ManifoldOneForm Plane M} (hΓ : SmoothOneFormFamily Γ)
    (hN : ∀ p, ∀ x ∈ D.chart.target, ContDiffAt ℝ ∞
      (fun q : P × Plane => chartOneForm (N q.1) x q.2) (p,extChartAt 𝓘(ℝ,Plane) x x))
    (hcurv : ∀ p, ∀ x ∈ D.chart.target,
      manifoldExteriorOneForm (Γ p) x = manifoldExteriorOneForm (N p) x) :
    SmoothOneFormFamily (annularNormalizeOf D b Γ N) ∧
      (∀ p x, x ∉ tsupport D.dual ∪ D.chart '' band (annularCutWidth D (annularCutWidth D b)) →
        annularNormalizeOf D b Γ N p x = Γ p x) ∧
      (∀ p x, manifoldExteriorOneForm (annularNormalizeOf D b Γ N p) x =
        manifoldExteriorOneForm (Γ p) x) ∧
      (∀ p x, x ∈ annularNormalizeRegion D b → annularNormalizeOf D b Γ N p x = N p x) := by
  let α := annularDifference D Γ N
  let F := annularPotential D Γ N
  let χ := annularCutoff D (annularCutWidth D b)
  let G : P × M → ℝ := fun q => χ q.2 * F q
  let a := cylinderFormPeriod 0 α
  have hc : annularCutWidth D b < D.width := by dsimp [annularCutWidth]; linarith
  have hβ (c : M) : ContDiffOn ℝ ∞ (chartOneForm D.dual c)
      (extChartAt 𝓘(ℝ,Plane) c).target :=
    (D.dual_smooth c).comp (f := fun y => ((0:ℝ), y))
      (contDiffOn_const.prodMk contDiffOn_id) (fun _ hy => ⟨mem_univ _, hy⟩)
  have ha0 : (0:ℝ) ∈ Ioo (-D.width) D.width := ⟨by linarith [D.width_pos], D.width_pos⟩
  have hpot := annularPotential_spec isOpen_univ isOpen_Ioo (convex_Ioo _ _) ha0
    D.chart D.source_eq hΓ (fun p _ x hx => hN p x hx)
    (fun p _ x hx => hcurv p x hx) D.clock_smooth D.clock_integral D.dual_pullback
  have hF : ContMDiffOn ((𝓘(ℝ,P)).prod 𝓘(ℝ,Plane)) 𝓘(ℝ,ℝ) ∞ F (univ ×ˢ D.chart.target) := hpot.1
  have hFd : ∀ p x, x ∈ D.chart.target →
      manifoldScalarDifferential (E := Plane) (fun y => F (p,y)) x = Γ p x-N p x-a p • D.dual x :=
    fun p x hx => hpot.2.2 p (mem_univ _) x hx
  have hχ : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,ℝ) ∞ χ := annularCutoff_smooth D hc
  have hχtarget : tsupport χ ⊆ D.chart.target :=
    (annularCutoff_support D hc).trans
      (D.image_band_subset_target (by dsimp [annularCutWidth]; linarith))
  have hG := manifoldFamily_local_potential_smoothOn isOpen_univ D.chart.open_target hF hχ hχtarget
  have hGs (p : P) : tsupport (fun x => G (p,x)) ⊆ tsupport χ :=
    scalar_product_tsupport_left (fun x => F (p,x)) χ
  have hχone (x : M) (hx : x ∈ annularNormalizeRegion D b) : χ x = 1 := by
    apply annularCutoff_one D hc
    exact ⟨D.chart.symm x, ⟨⟨hx.2.1.le, hx.2.2.le⟩, mem_univ _⟩, D.chart.right_inv hx.1⟩
  have hGd (p : P) (x : M) (hx : x ∈ annularNormalizeRegion D b) :
      manifoldScalarDifferential (E := Plane) (fun y => G (p,y)) x =
        manifoldScalarDifferential (E := Plane) (fun y => F (p,y)) x := by
    apply Filter.EventuallyEq.mfderiv_eq
    filter_upwards [(annularNormalizeRegion_open D b).mem_nhds hx] with y hy
    change χ y * F (p,y) = F (p,y)
    rw [hχone y hy, one_mul]
  have ha : ContDiff ℝ ∞ a := contDiffOn_univ.mp hpot.2.1
  refine ⟨normalizedManifoldPrimitive_smooth isOpen_univ hΓ hβ ha.contDiffOn hG, ?_, ?_, ?_⟩
  · intro p x hx
    have hβz : D.dual x = 0 := notMem_support.mp (fun hh => hx (Or.inl (subset_closure hh)))
    have hdz : manifoldScalarDifferential (E := Plane) (fun y => G (p,y)) x = 0 := by
      apply notMem_support.mp
      intro hh
      exact hx (Or.inr ((annularCutoff_support D hc) ((hGs p) (manifoldScalarDifferential_support _ hh))))
    change Γ p x-a p • D.dual x-manifoldScalarDifferential (E := Plane) (fun y => G (p,y)) x = Γ p x
    rw [hβz, hdz, smul_zero, sub_zero, sub_zero]
  · intro p x
    have hΓp (c : M) : ContDiffOn ℝ ∞ (chartOneForm (Γ p) c)
        (extChartAt 𝓘(ℝ,Plane) c).target :=
      (hΓ c).comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y hy => ⟨mem_univ _,hy⟩)
    exact manifold_closed_exact_normalization hΓp hβ D.dual_closed
      (manifoldFamily_scalar_fiber_smooth isOpen_univ hG (mem_univ p)) (a p) x
  · intro p x hx
    change Γ p x-a p • D.dual x-manifoldScalarDifferential (E := Plane) (fun y => G (p,y)) x = N p x
    rw [hGd p x hx, hFd p x hx.1]
    apply ContinuousLinearMap.ext
    intro v
    change Γ p x v-a p*D.dual x v-(Γ p x v-N p x v-a p*D.dual x v) = N p x v
    ring

end SymplecticPacking.HighDim.ToricPackingStages
