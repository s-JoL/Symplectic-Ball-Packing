import SymplecticPacking.BranchLarge3.OAIOpen
import SymplecticPacking.BranchLarge3.TargetMoser

/-!
# Step S8: explicit embedding of the degree-`ℓ` affine form into the standard ball

Explicit version of the OpenAI theorem `Hamiltonian.exists_degree_polynomial_target_embedding`:
for a homogeneous polynomial map `P` of degree `ℓ` without nontrivial zeros, and `0 ≤ d`,
`ℓ d < 1`, an explicit smooth embedding `g : ℂⁿ → ℂⁿ` into the open ball of capacity `π c`
pulling the standard form back to `degreeAffineForm ℓ P c d`.

* S8a (`moserF`, `moserG`): the explicit global Moser diffeomorphism pair between
  `degreeAffineForm ℓ P c d` and `degreeAffineForm ℓ P c 0` (OpenAI
  `exists_degree_global_affine_moser`; linear interpolation of the potentials, time-1 flow of the
  Moser field, its inverse flow).
* S8 (`targetMap`, proved from S8a): `targetMap = Φ⁻¹ ∘ fsBallMap c ∘ Φ ∘ moserG`, the radial
  Fubini–Study shell `fsBallMap` composed with the Moser map (OpenAI
  `BallMaps/SphereCartesianDescent`).

Paper: main `lem:sxr-shell`, supplement `six-return.tex`.
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3

open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff
open Function

/-- S8a: the explicit global Moser map `f` (from `d = 0` to `d`). -/
def moserF {ι κ : Type} [Fintype ι] [Fintype κ] (P : (Option ι → ℂ) → (κ → ℂ)) (ℓ : ℕ)
    (c d : ℝ) : (ι → ℂ) → (ι → ℂ) :=
  sphereAffineDescend (complexConjugate (TargetMoser.shellF P ℓ c d))

/-- S8a: the explicit global Moser map `g` (inverse of `moserF`). -/
def moserG {ι κ : Type} [Fintype ι] [Fintype κ] (P : (Option ι → ℂ) → (κ → ℂ)) (ℓ : ℕ)
    (c d : ℝ) : (ι → ℂ) → (ι → ℂ) :=
  sphereAffineDescend (complexConjugate (TargetMoser.shellG P ℓ c d))

theorem moser_spec {ι κ : Type} [Fintype ι] [Fintype κ] {P : (Option ι → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℂ ∞ P) (hPn : ∀ z, z ≠ 0 → P z ≠ 0)
    {ℓ : ℕ} (hPs : ∀ (ζ : ℂ) z, P (ζ • z) = ζ ^ ℓ • P z)
    {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hdℓ : (ℓ : ℝ) * d < 1) :
    let f := moserF P ℓ c d
    let g := moserG P ℓ c d
    ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ g ∧ LeftInverse g f ∧ RightInverse g f ∧
      (∀ x v w, degreeAffineForm (ℓ : ℝ) P c d (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) =
        degreeAffineForm (ℓ : ℝ) P c 0 x v w) ∧
      (∀ x v w, degreeAffineForm (ℓ : ℝ) P c 0 (g x) (fderiv ℝ g x v) (fderiv ℝ g x w) =
        degreeAffineForm (ℓ : ℝ) P c d x v w) := by
  intro f g
  have H : TargetMoser.Hyp P ℓ c d := ⟨hP, hPn, hPs, hc, hd, hdℓ⟩
  have hPr := hP.restrict_scalars ℝ
  have hfinf (z : PlanePhase (Option ι)) (_hz : phaseSq z = 1) :
      complexCartesian.symm (TargetMoser.shellF P ℓ c d z) none = 0 ↔
        complexCartesian.symm z none = 0 := by
    simpa only [phaseInfinity_complex_range] using H.shellF_range z
  have hginf (z : PlanePhase (Option ι)) (_hz : phaseSq z = 1) :
      complexCartesian.symm (TargetMoser.shellG P ℓ c d z) none = 0 ↔
        complexCartesian.symm z none = 0 := by
    simpa only [phaseInfinity_complex_range] using H.shellG_range z
  have hfζ (ζ : ℂ) (hζ : Complex.normSq ζ = 1) (z : PlanePhase (Option ι)) (_hz : phaseSq z = 1) :
      TargetMoser.shellF P ℓ c d (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z) =
        phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (TargetMoser.shellF P ℓ c d z) := by
    simp only [phaseUnitDiagonal_eq_rotate]
    exact H.shellF_rot ζ.arg z
  have hgζ (ζ : ℂ) (hζ : Complex.normSq ζ = 1) (z : PlanePhase (Option ι)) (_hz : phaseSq z = 1) :
      TargetMoser.shellG P ℓ c d (phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) z) =
        phaseUnitDiagonal (fun _ => ζ) (fun _ => hζ) (TargetMoser.shellG P ℓ c d z) := by
    simp only [phaseUnitDiagonal_eq_rotate]
    exact H.shellG_rot ζ.arg z
  obtain ⟨hfC, hgC, hgfC, hfgC⟩ := sphereCartesianDescend_equiv H.shellF_smooth H.shellG_smooth
    H.shell_left H.shell_right H.shellF_sq H.shellG_sq hfinf hginf hfζ hgζ
  have hωC (x v w : ι → ℂ) :
      degreeAffineForm (ℓ : ℝ) P c d (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) =
        degreeAffineForm (ℓ : ℝ) P c 0 x v w := by
    change degreeAffineForm (ℓ : ℝ) P c d
        (sphereAffineDescend (complexConjugate (TargetMoser.shellF P ℓ c d)) x)
        (fderiv ℝ (sphereAffineDescend (complexConjugate (TargetMoser.shellF P ℓ c d))) x v)
        (fderiv ℝ (sphereAffineDescend (complexConjugate (TargetMoser.shellF P ℓ c d))) x w) = _
    rw [degreeAffineForm_pullback hPr (hfC.differentiable (by simp) x), degreeAffineForm_apply]
    exact sphereAffineDescend_degree_curvature hPr hPn hPs H.shellF_smooth H.shellF_sq hfinf c d
      (fun z hz v w => H.shell_form z hz v w) x v w
  exact ⟨hfC, hgC, hgfC, hfgC, hωC,
    diffeomorphicFormPullback_inverse hfC hgC hfgC (degreeAffineForm (ℓ : ℝ) P c 0)
      (degreeAffineForm (ℓ : ℝ) P c d) hωC⟩

/-- S8: the explicit shell embedding. -/
def targetMap {n : ℕ} {κ : Type} [Fintype κ] (P : (Option (Fin n) → ℂ) → (κ → ℂ)) (ℓ : ℕ)
    (c d : ℝ) : Ambient n → Ambient n := fun x =>
  complexCartesian.symm (fsBallMap c (complexCartesian (moserG P ℓ c d x)))

theorem targetMap_spec {n : ℕ} {κ : Type} [Fintype κ]
    {P : (Option (Fin n) → ℂ) → (κ → ℂ)}
    (hP : ContDiff ℂ ∞ P) (hPn : ∀ z, z ≠ 0 → P z ≠ 0)
    {ℓ : ℕ} (hPs : ∀ (ζ : ℂ) z, P (ζ • z) = ζ ^ ℓ • P z)
    {c d : ℝ} (hc : 0 < c) (hd : 0 ≤ d) (hdℓ : (ℓ : ℝ) * d < 1) :
    let g := targetMap P ℓ c d
    ContDiff ℝ ∞ g ∧ Topology.IsEmbedding g ∧
      (∀ x, g x ∈ openBall n (Real.pi * c)) ∧
      ∀ x v w, standardForm (fderiv ℝ g x v) (fderiv ℝ g x w) =
        degreeAffineForm (ℓ : ℝ) P c d x v w := by
  intro h
  obtain ⟨hf, hg, hgf, hfg, _hfω, hgω⟩ := moser_spec hP hPn hPs hc hd hdℓ
  set f := moserF P ℓ c d
  set g := moserG P ℓ c d
  let e : Ambient n ≃ₜ Ambient n :=
    { toEquiv := ⟨g, f, hfg, hgf⟩
      continuous_toFun := hg.continuous
      continuous_invFun := hf.continuous }
  have hh : ContDiff ℝ ∞ h := (complexCartesian (ι := Fin n)).symm.contDiff.comp
    ((fsBallMap_smooth c).comp ((complexCartesian (ι := Fin n)).contDiff.comp hg))
  refine ⟨hh, complexCartesian.symm.toHomeomorph.isEmbedding.comp
    ((fsBallMap_isEmbedding hc).comp (complexCartesian.toHomeomorph.isEmbedding.comp e.isEmbedding)),
    fun x => complexRadialTarget_mem hc (g x), ?_⟩
  intro x v w
  have hD (u : Ambient n) : fderiv ℝ h x u = complexCartesian.symm
      (fderiv ℝ (fsBallMap c) (complexCartesian (g x)) (complexCartesian (fderiv ℝ g x u))) := by
    exact congrArg (fun L => L u) ((complexCartesian.symm.hasFDerivAt.comp x
      (((fsBallMap_smooth c).differentiable (by simp) _).hasFDerivAt.comp x
        (complexCartesian.hasFDerivAt.comp x (hg.differentiable (by simp) x).hasFDerivAt))).fderiv)
  rw [hD, hD, complexCartesian_standardForm]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [fsBallMap_pullback hc.le, ← degreeAffineForm_zero (ℓ : ℝ) P c, hgω]

end SymplecticPacking.BranchLarge3
