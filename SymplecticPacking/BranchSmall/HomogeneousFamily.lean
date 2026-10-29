import SymplecticPacking.BranchSmall.HomogeneousReturn

/-!
# Smooth families of homogeneous cone fields

The polynomial may vary smoothly with a parameter. All inverses here are the
nondegenerate form inverses; smoothness is local on the punctured cone.
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT
open Set Filter Topology Function ContinuousLinearMap
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff

set_option maxHeartbeats 800000

section calculus
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fibrePrimitivePullback_contDiffAt {α : F → F →L[ℝ] ℝ} {G : ℝ × E → F}
    (hG : ContDiff ℝ ∞ G) {p : ℝ × E} (hα : ContDiffAt ℝ ∞ α (G p)) :
    ContDiffAt ℝ ∞ (fun p : ℝ × E => primitivePullback α (fun x => G (p.1, x)) p.2) p := by
  have he (p : ℝ × E) : primitivePullback α (fun x => G (p.1, x)) p.2 =
      (primitivePullback α G p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    have hi : HasFDerivAt (fun x : E => (p.1, x)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 := by
      convert! (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id p.2) using 1
    have hd := (hG.differentiable (by simp) p).hasFDerivAt.comp p.2 hi
    unfold primitivePullback
    rw [show fderiv ℝ (fun x => G (p.1, x)) p.2 = _ from hd.fderiv]
    rfl
  simp_rw [he]
  exact (primitivePullback_smoothAt hα hG.contDiffAt).clm_comp contDiffAt_const

/-- Exterior differentiation in the spatial variable preserves joint smoothness locally. -/
theorem spatialExterior_contDiffOn [FiniteDimensional ℝ E] {U : Set (ℝ × E)} (hU : IsOpen U)
    {α : ℝ → E → E →L[ℝ] ℝ}
    (hα : ContDiffOn ℝ ∞ (fun p : ℝ × E => α p.1 p.2) U) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => euclideanExteriorOneForm (α p.1) p.2) U := by
  let D : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ := fun p =>
    (fderiv ℝ (fun p : ℝ × E => α p.1 p.2) p).comp (ContinuousLinearMap.inr ℝ ℝ E)
  have hD : ContDiffOn ℝ ∞ D U :=
    (hα.fderiv_of_isOpen (m := ∞) hU (by simp)).clm_comp contDiffOn_const
  have hfl : ContDiffOn ℝ ∞ (fun p => (D p).flip) U := by
    apply contDiffOn_clm_apply.mpr
    intro u
    apply contDiffOn_clm_apply.mpr
    intro v
    change ContDiffOn ℝ ∞ (fun p => D p v u) U
    exact (hD.clm_apply contDiffOn_const).clm_apply contDiffOn_const
  apply (hD.sub hfl).congr
  intro p hp
  have hi : HasFDerivAt (fun x : E => (p.1, x)) (ContinuousLinearMap.inr ℝ ℝ E) p.2 := by
    convert! (hasFDerivAt_const (𝕜 := ℝ) p.1 p.2).prodMk (hasFDerivAt_id p.2) using 1
  have hd := ((hα.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)).hasFDerivAt.comp p.2 hi
  change HasFDerivAt (α p.1) (D p) p.2 at hd
  change euclideanExteriorOneForm (α p.1) p.2 = D p - (D p).flip
  unfold euclideanExteriorOneForm
  rw [hd.fderiv]

end calculus

section family
variable {ι κ : Type} [Fintype ι] [Fintype κ]
local notation "HIn" => PlanePhase ι
local notation "HOut" => PlanePhase κ

private theorem punctured_isOpen : IsOpen ((univ : Set ℝ) ×ˢ ({z : HIn | z ≠ 0})) :=
  isOpen_univ.prod isOpen_ne

theorem homogeneousConePrimitive_family_contDiffOn {P : ℝ × HIn → HOut}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ (s : ℝ) (z : HIn), z ≠ 0 → P (s, z) ≠ 0) (c d : ℝ) :
    ContDiffOn ℝ ∞ (fun p : ℝ × HIn => homogeneousConePrimitive (fun z => P (p.1, z)) c d p.2)
      (univ ×ˢ ({z : HIn | z ≠ 0})) := by
  intro p hp
  have hbase : ContDiffAt ℝ ∞ (fun p : ℝ × HIn => hopfPrimitive c p.2) p :=
    (hopfPrimitive_smoothAt c hp.2).comp p contDiffAt_snd
  have hpull := fibrePrimitivePullback_contDiffAt hP (hopfPrimitive_smoothAt c (hPn p.1 p.2 hp.2))
  have hmix := (hbase.const_smul (1 - 2 * d)).add (hpull.const_smul d)
  exact (((phaseSq_smooth.comp contDiff_snd).contDiffAt).smul hmix).contDiffWithinAt

theorem homogeneousConeField_family_contDiffOn {P : ℝ × HIn → HOut}
    (hP : ContDiff ℝ ∞ P) (hPn : ∀ (s : ℝ) (z : HIn), z ≠ 0 → P (s, z) ≠ 0)
    (hD : ∀ (s : ℝ) (z : HIn), fderiv ℝ (fun z => P (s, z)) z z = (2 : ℝ) • P (s, z))
    (hJ : ∀ (s : ℝ) (z v : HIn), fderiv ℝ (fun z => P (s, z)) z (phaseJ v) =
      phaseJ (fderiv ℝ (fun z => P (s, z)) z v))
    {c d : ℝ} (hc : 0 < c) (hd0 : 0 ≤ d) (hd : d < 1 / 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × HIn => homogeneousConeField (fun z => P (p.1, z)) c d 1 p.2)
      (univ ×ˢ ({z : HIn | z ≠ 0})) := by
  have hLam := homogeneousConePrimitive_family_contDiffOn (P := P) hP hPn c d
  have hLam0 := homogeneousConePrimitive_family_contDiffOn (P := P) hP hPn c 0
  have hΩ := spatialExterior_contDiffOn (E := HIn)
    (U := (univ : Set ℝ) ×ˢ ({z : HIn | z ≠ 0}))
    (α := fun (s : ℝ) (z : HIn) => homogeneousConePrimitive (fun w : HIn => P (s, w)) c d z)
    (isOpen_univ.prod isOpen_ne) hLam
  intro p hp
  have hPp : ContDiff ℝ ∞ (fun z => P (p.1, z)) :=
    hP.comp (contDiff_const.prodMk contDiff_id)
  have hi := homogeneousConePrimitive_nondegenerate (F := fun z => P (p.1, z)) (z := p.2)
    hPp.contDiffAt hp.2 (hPn _ _ hp.2) (hD p.1 p.2) (hJ p.1 p.2) hc hd0 hd
  have hΩp := hΩ.contDiffAt (punctured_isOpen.mem_nhds hp)
  have hβp := (hLam.sub hLam0).contDiffAt (punctured_isOpen.mem_nhds hp)
  have hinv := hi.contDiffAt_map_inverse.comp p hΩp
  simpa only [homogeneousConeField, one_mul, Function.comp_apply, ContinuousLinearMap.neg_apply] using
    (hinv.clm_apply hβp).neg.contDiffWithinAt (s := univ ×ˢ ({z : HIn | z ≠ 0}))

end family

section quadric
variable {m : ℕ} {T : ℝ → ℝ}

theorem homogeneousPolynomial_parameter_contDiff (a : Fin m → ℂ)
    (hT : ContDiff ℝ ∞ T) (hT0 : ∀ s, T s ≠ 0) :
    ContDiff ℝ ∞ (fun p : ℝ × HomogeneousInput m => homogeneousPolynomial a (T p.1) p.2) := by
  have hI : ContDiff ℝ ∞ (fun p : ℝ × HomogeneousInput m => ((T p.1 : ℝ) : ℂ)⁻¹) :=
    (Complex.ofRealCLM.contDiff.comp (hT.comp contDiff_fst)).inv
      (fun p => Complex.ofReal_ne_zero.mpr (hT0 p.1))
  apply contDiff_pi.mpr
  rintro (_|((⟨e,i⟩|⟨i,j⟩)|j))
  · exact ((contDiff_apply ℝ ℂ none).comp contDiff_snd).pow 2
  · exact ((contDiff_apply ℝ ℂ none).comp contDiff_snd).mul
      ((contDiff_apply ℝ ℂ (some i)).comp contDiff_snd)
  · exact ((contDiff_apply ℝ ℂ (some i)).comp contDiff_snd).mul
      ((contDiff_apply ℝ ℂ (some j)).comp contDiff_snd)
  · exact hI.mul ((((contDiff_apply ℝ ℂ (some (some j))).comp contDiff_snd).pow 2).sub
      (((contDiff_apply ℝ ℂ (some none)).comp contDiff_snd).pow 2) |>.add
      (contDiff_const.mul (((contDiff_apply ℝ ℂ none).comp contDiff_snd).pow 2)))

theorem homogeneousCartesian_parameter_contDiff (a : Fin m → ℂ)
    (hT : ContDiff ℝ ∞ T) (hT0 : ∀ s, T s ≠ 0) :
    ContDiff ℝ ∞ (fun p : ℝ × PlanePhase (Option (Option (Fin m))) =>
      homogeneousCartesian a (T p.1) p.2) := by
  exact complexCartesian.contDiff.comp ((homogeneousPolynomial_parameter_contDiff a hT hT0).comp
    (contDiff_fst.prodMk (complexCartesian.symm.contDiff.comp contDiff_snd)))

theorem normalPolynomial_parameter_contDiff (a : Fin m → ℂ)
    (hT : ContDiff ℝ ∞ T) (hT0 : ∀ s, T s ≠ 0) :
    ContDiff ℝ ∞ (fun p : ℝ × Affine m => normalPolynomial a (T p.1) p.2) := by
  have hI : ContDiff ℝ ∞ (fun p : ℝ × Affine m => ((T p.1 : ℝ) : ℂ)⁻¹) :=
    (Complex.ofRealCLM.contDiff.comp (hT.comp contDiff_fst)).inv
      (fun p => Complex.ofReal_ne_zero.mpr (hT0 p.1))
  have hV := ((veronese_contDiff.comp (affineComplex m).contDiff).restrict_scalars ℝ).comp
    (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × Affine m → Affine m))
  have hE := ((equations_contDiff a).restrict_scalars ℝ).comp
    (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : ℝ × Affine m → Affine m))
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i => exact (contDiff_apply ℝ ℂ i).comp hV
  | inr j => exact hI.mul ((contDiff_apply ℝ ℂ j).comp hE)

theorem normalAmbientPrimitive_parameter_contDiff (a : Fin m → ℂ)
    (hT : ContDiff ℝ ∞ T) (hT0 : ∀ s, T s ≠ 0) (c d : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Affine m => normalAmbientPrimitive a c d (T p.1) p.2) := by
  let G : ℝ × Affine m → PlanePhase (NormalPolynomialIndex m) := fun p =>
    complexCartesian (normalPolynomial a (T p.1) p.2)
  have hG : ContDiff ℝ ∞ G :=
    (complexCartesian (ι := NormalPolynomialIndex m)).contDiff.comp
      (normalPolynomial_parameter_contDiff a hT hT0)
  have hPB : ContDiff ℝ ∞ (fun p : ℝ × Affine m =>
      primitivePullback (affineFSPrimitive c) (fun z => G (p.1, z)) p.2) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    exact fibrePrimitivePullback_contDiffAt hG (affineFSPrimitive_smooth c).contDiffAt
  exact (((ambientFSPrimitive_smooth (m := m) c).comp contDiff_snd).const_smul (1 - 2 * d)).add
    (hPB.const_smul d)

theorem homogeneousConeField_parameter_contDiffOn (a : Fin m → ℂ)
    (hT : ContDiff ℝ ∞ T) (hT0 : ∀ s, T s ≠ 0) {c b : ℝ}
    (hc : 0 < c) (hb0 : 0 ≤ b) (hb : b < 1 / 2) :
    ContDiffOn ℝ ∞ (fun p : ℝ × PlanePhase (Option (Option (Fin m))) =>
      homogeneousConeField (homogeneousCartesian a (T p.1)) c b 1 p.2)
      (univ ×ˢ ({z : PlanePhase (Option (Option (Fin m))) | z ≠ 0})) := by
  exact homogeneousConeField_family_contDiffOn (homogeneousCartesian_parameter_contDiff a hT hT0)
    (fun s z hz => homogeneousCartesian_nonzero a (T s) hz)
    (fun s z => homogeneousCartesian_euler a (T s) z)
    (fun s z v => homogeneousCartesian_J a (T s) z v) hc hb0 hb

end quadric

end SymplecticPacking.BranchSmall.VT
