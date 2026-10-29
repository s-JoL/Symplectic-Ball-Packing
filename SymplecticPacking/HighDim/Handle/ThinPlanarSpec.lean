import SymplecticPacking.HighDim.Handle.LayerMapsDef
import OAI.Geometry.BallPacking.Moser.DiskMoser

/-!
# The thin planar strip map is a symplectic embedding

The explicit strip map is an open symplectic embedding of the entire plane.
-/

noncomputable section
set_option maxHeartbeats 800000

namespace SymplecticPacking.HighDim.ToricPackingStages

open Set Function
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology

theorem thinPlanar_eq_conjugate (δ : ℝ) :
    thinPlanar δ = Complex.equivRealProdCLM ∘ Strip.psiStrip δ ∘ Complex.equivRealProdCLM.symm := by
  funext x
  rfl

theorem thinPlanar_fderiv {δ : ℝ} (hδ : 0 < δ) (x : Plane) :
    fderiv ℝ (thinPlanar δ) x =
      Complex.equivRealProdCLM.toContinuousLinearMap.comp
        ((fderiv ℝ (Strip.psiStrip δ) (Complex.equivRealProdCLM.symm x)).comp
          Complex.equivRealProdCLM.symm.toContinuousLinearMap) := by
  rw [thinPlanar_eq_conjugate]
  rw [fderiv_comp x Complex.equivRealProdCLM.differentiableAt
    (((Strip.psiStrip_smooth hδ).differentiable (by simp) _).comp x
      Complex.equivRealProdCLM.symm.differentiableAt)]
  rw [fderiv_comp x ((Strip.psiStrip_smooth hδ).differentiable (by simp) _)
    Complex.equivRealProdCLM.symm.differentiableAt]
  simp only [ContinuousLinearEquiv.fderiv]

theorem thinPlanar_det {δ : ℝ} (hδ : 0 < δ) (x : Plane) :
    (fderiv ℝ (thinPlanar δ) x).det = 1 := by
  rw [thinPlanar_fderiv hδ]
  change LinearMap.det ((Complex.equivRealProdCLM.toLinearEquiv.toLinearMap).comp
    ((fderiv ℝ (Strip.psiStrip δ) (Complex.equivRealProdCLM.symm x)).toLinearMap.comp
      Complex.equivRealProdCLM.symm.toLinearEquiv.toLinearMap)) = 1
  have h := LinearMap.det_conj
    (fderiv ℝ (Strip.psiStrip δ) (Complex.equivRealProdCLM.symm x)).toLinearMap
    Complex.equivRealProdCLM.toLinearEquiv
  exact h.trans ((Strip.psiStrip_normalize hδ).2.1 _)

theorem thinPlanar_symplectic {δ : ℝ} (hδ : 0 < δ) (x v w : Plane) :
    planarArea (fderiv ℝ (thinPlanar δ) x v) (fderiv ℝ (thinPlanar δ) x w) =
      planarArea v w := by
  rw [planarArea_map, thinPlanar_det hδ, one_mul]

theorem thinPlanar_injective {δ : ℝ} (hδ : 0 < δ) : Injective (thinPlanar δ) := by
  intro x y hxy
  have hp : Strip.psiStrip δ (Complex.equivRealProdCLM.symm x) =
      Strip.psiStrip δ (Complex.equivRealProdCLM.symm y) := by
    apply Complex.equivRealProdCLM.injective
    exact hxy
  exact Complex.equivRealProdCLM.symm.injective
    ((Strip.psiStrip_bijOn hδ).2.1 (mem_univ _) (mem_univ _) hp)

theorem thinPlanar_isOpenEmbedding {δ : ℝ} (hδ : 0 < δ) :
    Topology.IsOpenEmbedding (thinPlanar δ) := by
  have hiv (x : Plane) : (fderiv ℝ (thinPlanar δ) x).IsInvertible := by
    let A := fderiv ℝ (thinPlanar δ) x
    have hdet : IsUnit A.toLinearMap.det := by
      rw [show A.toLinearMap.det = 1 from thinPlanar_det hδ x]
      exact isUnit_one
    let e := (LinearMap.equivOfIsUnitDet hdet).toContinuousLinearEquiv
    refine ⟨e, ?_⟩
    apply ContinuousLinearMap.ext
    intro v
    exact LinearMap.equivOfIsUnitDet_apply hdet v
  choose e he using hiv
  have hopen : IsOpenMap (thinPlanar δ) := isOpenMap_of_hasStrictFDerivAt_equiv (fun x => by
    rw [he x]
    exact (thinPlanar_smooth hδ).hasStrictFDerivAt (by simp))
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (thinPlanar_smooth hδ).continuous (thinPlanar_injective hδ) hopen

theorem thinProduct_smooth {ι : Type*} [Fintype ι] {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (thinProduct (ι := ι) δ) :=
  ((thinPlanar_smooth hδ).comp contDiff_fst).prodMk contDiff_snd

theorem thinProduct_isEmbedding {ι : Type*} [Fintype ι] {δ : ℝ} (hδ : 0 < δ) :
    Topology.IsEmbedding (thinProduct (ι := ι) δ) :=
  (thinPlanar_isOpenEmbedding hδ).isEmbedding.prodMap Topology.IsEmbedding.id

theorem thinProduct_fderiv {ι : Type*} [Fintype ι] {δ : ℝ} (hδ : 0 < δ)
    (p v : Plane × PlanePhase ι) :
    fderiv ℝ (thinProduct (ι := ι) δ) p v = (fderiv ℝ (thinPlanar δ) p.1 v.1, v.2) := by
  have hd := (((thinPlanar_smooth hδ).differentiable (by simp) p.1).hasFDerivAt.comp p
    (hasFDerivAt_fst (𝕜 := ℝ) (p := p))).prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := p))
  change HasFDerivAt (thinProduct (ι := ι) δ) _ p at hd
  rw [hd.fderiv]
  rfl

theorem thinProduct_symplectic {ι : Type*} [Fintype ι] {δ : ℝ} (hδ : 0 < δ)
    (p v w : Plane × PlanePhase ι) :
    productForm phaseArea (fderiv ℝ (thinProduct δ) p v) (fderiv ℝ (thinProduct δ) p w) =
      productForm phaseArea v w := by
  rw [thinProduct_fderiv hδ, thinProduct_fderiv hδ]
  simp only [productForm_apply]
  rw [thinPlanar_symplectic hδ]

end SymplecticPacking.HighDim.ToricPackingStages
