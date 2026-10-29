import SymplecticPacking.BranchLargeHigh.SecondStageMaps
import SymplecticPacking.BranchLargeHigh.PrimitiveLeibniz
import SymplecticPacking.BranchLargeHigh.LiftPhaseDerivative

/-!
# The pullback identity of the return map (supplement `lem:two-identification`, `lem:two-mixed`)

Supporting lemmas for `Two.returnMap'_pullback` (`ReturnMapSpec.lean`). Write
`T(b, ζ) = (b, tail(unmix ζ))` for the tube coordinates, `φ` for the vector transfer, `Ψ` for the
lift phase, `λ = φ^*λ_base`, and

  `ℓ = Σ_j v_j dθ_j + (1 − 2Σ_j v_j) P`   (`canonPrim`, `P = curveFSPrimitive`)

for the canonical primitive of the transfer model form `Ω_X = quadricForm`. Then:

* `chartLift_pullback_of` (proved): if `dΨ = λ − ℓ` at `T x`, then at `x`
  `R^*Ω = ω_fib + (1 − u) T^*Ω_X − du ∧ T^*ℓ`
  (chain rule; `φ^*ω₀ = Ω_X` is `BranchSmall.vectorTransfer_spec`; the rotation
  `z₀ ↦ e^{2πiΨ} z₀` contributes `du ∧ dΨ`).
* `liftPhase_mfderiv` (`lem:two-identification` (iv),(v)): `dΨ = λ − ℓ` on the tube.
* `mixedModel_form_eq` (`lem:two-mixed` (ii)): `Ω_mix = ω_fib + (1 − u) T^*Ω_X − du ∧ T^*ℓ`
  on `u < 1`.
-/

noncomputable section

namespace SymplecticPacking.BranchLargeHigh.Two

open Set Filter Topology Manifold Problem
open SymplecticPacking.HighDim
open OAI.PackingSufficiencySupport (Ambient)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold

variable {k : ℕ}

/-- The tube coordinates `T(b, ζ) = (b, tail(unmix ζ))` (equal to `tubeCoord`). -/
def tubeMap {q : ℕ} (x : Surface q × Fibre (q + 3)) : Surface q × Fibre (q + 2) :=
  (x.1, tailFibre (unmix x.2))

/-- The canonical primitive `ℓ = Σ_j v_j dθ_j + (1 − 2Σ_j v_j) P` of `Ω_X = quadricForm`
(`Σ_j v_j dθ_j = ½ phaseArea(w, ·)`, `P = curveFSPrimitive`). -/
def canonPrim (q : ℕ) (y : Surface q × Fibre (q + 2)) (t : (ℝ × ℝ) × Fibre (q + 2)) : ℝ :=
  phaseArea y.2 t.2 / 2 +
    equalNormalCoefficient (q + 2) 2 (planeMoments y.2) *
      curveFSPrimitive (parameters q) (1 / Real.pi) y.1 t.1

theorem normalCouplingPrimitive_canonPrim (q : ℕ) (y : Surface q × Fibre (q + 2))
    (t : (ℝ × ℝ) × Fibre (q + 2)) :
    normalCouplingPrimitive (parameters q) y t = canonPrim q y t := by
  rw [normalCouplingPrimitive_apply]
  simp only [canonPrim, standardLiouville, smul_apply, smul_eq_mul, equalNormalCoefficient,
    phaseMoments_sum]
  ring

/-- `du_ζ(t) = 2π ⟨ζ₀, t₀⟩` for `u = π|ζ₀|²`. -/
def dUMom {q : ℕ} (ζ t : Fibre (q + 3)) : ℝ :=
  2 * Real.pi * ((ζ 0).1 * (t 0).1 + (ζ 0).2 * (t 0).2)

/-- The area form `dx₀ ∧ dy₀` of the first plane. -/
def planeArea0 {q : ℕ} (s t : Fibre (q + 3)) : ℝ :=
  (s 0).1 * (t 0).2 - (s 0).2 * (t 0).1

/-- The right-hand side `ω_fib + (1 − u) T^*Ω_X − du ∧ T^*ℓ` at `x`. -/
def mixedRHS {q : ℕ} (x : Surface q × Fibre (q + 3)) (v w : (ℝ × ℝ) × Fibre (q + 3)) : ℝ :=
  planeArea0 v.2 w.2 +
    (1 - uMom x.2) * BranchSmall.quadricForm q (tubeMap x)
      (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) tubeMap x v)
      (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) tubeMap x w) -
    dUMom x.2 v.2 * canonPrim q (tubeMap x)
      (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) tubeMap x w) +
    dUMom x.2 w.2 * canonPrim q (tubeMap x)
      (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) tubeMap x v)

/-! ### Elementary complex algebra -/

lemma cross_mul_rot {E X Y : ℂ} (hE : Complex.normSq E = 1) :
    (E * X).re * (E * Y).im - (E * X).im * (E * Y).re = X.re * Y.im - X.im * Y.re := by
  rw [Complex.normSq_apply] at hE
  simp only [Complex.mul_re, Complex.mul_im]
  linear_combination (X.re * Y.im - X.im * Y.re) * hE

lemma dot_mul_rot {E X Y : ℂ} (hE : Complex.normSq E = 1) :
    (E * X).re * (E * Y).re + (E * X).im * (E * Y).im = X.re * Y.re + X.im * Y.im := by
  rw [Complex.normSq_apply] at hE
  simp only [Complex.mul_re, Complex.mul_im]
  linear_combination (X.re * Y.re + X.im * Y.im) * hE

lemma normSq_exp_turn (t : ℝ) :
    Complex.normSq (Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))) = 1 := by
  have : 2 * Real.pi * Complex.I * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]

lemma planeC_eq_symm (p : ℝ × ℝ) : planeC p = Complex.equivRealProdCLM.symm p := by
  rw [Complex.equivRealProdCLM_symm_apply]
  apply Complex.ext <;> simp [planeC]

lemma rotX_re (z d : ℝ × ℝ) (a : ℝ) :
    (planeC d + planeC z * ((a : ℂ) * (2 * Real.pi * Complex.I))).re =
      d.1 - 2 * Real.pi * a * z.2 := by
  simp [planeC, Complex.mul_re, Complex.mul_im]; ring

lemma rotX_im (z d : ℝ × ℝ) (a : ℝ) :
    (planeC d + planeC z * ((a : ℂ) * (2 * Real.pi * Complex.I))).im =
      d.2 + 2 * Real.pi * a * z.1 := by
  simp [planeC, Complex.mul_re, Complex.mul_im]; ring

/-! ### Derivatives of the components of the return map -/

lemma srcModel_eq' {q : ℕ} :
    𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) = 𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, Fibre (q + 3)) :=
  modelWithCornersSelf_prod

lemma hasMFDerivAt_fib0 {q : ℕ} (x : Surface q × Fibre (q + 3)) :
    HasMFDerivAt 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, ℝ × ℝ)
      (fun x : Surface q × Fibre (q + 3) => x.2 0) x
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (q + 3) => ℝ × ℝ) 0).comp
        (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Fibre (q + 3)))) := by
  have h1 := hasMFDerivAt_snd (I := 𝓘(ℝ, ℝ × ℝ)) (I' := 𝓘(ℝ, Fibre (q + 3))) x
  have h2 : HasMFDerivAt 𝓘(ℝ, Fibre (q + 3)) 𝓘(ℝ, ℝ × ℝ) (fun ζ : Fibre (q + 3) => ζ 0) x.2
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (q + 3) => ℝ × ℝ) 0) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (q + 3) => ℝ × ℝ) 0).hasFDerivAt.hasMFDerivAt
  have h3 := h2.comp x h1
  rw [srcModel_eq']
  exact h3

/-- **Assembly** (chain rule): if `dΨ = λ − ℓ` at `T x`, the return map pulls the coupled form
back to `ω_fib + (1 − u) T^*Ω_X − du ∧ T^*ℓ` at `x`. -/
theorem chartLift_pullback_of {q : ℕ} {h₁ h₂ : ℝ} (hh : 0 < h₂) (hh2 : h₂ < 1 / 2)
    (x : Surface q × Fibre (q + 3))
    (hy : tubeMap x ∈ BranchSmall.transferDomain q (transferHeight h₂))
    (hT : MDifferentiableAt 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2))
      tubeMap x)
    (hΨ : MDifferentiableAt 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) 𝓘(ℝ, ℝ)
      (fun y : Surface q × Fibre (q + 2) => liftPhase q h₂ y.1 y.2) (tubeMap x))
    (hR : MDifferentiableAt 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, E (q + 4))
      (fun x => chartLiftExplicit q h₁ h₂ (Prod.map id unmix x)) x)
    (hP : ∀ t, mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) 𝓘(ℝ, ℝ)
        (fun y : Surface q × Fibre (q + 2) => liftPhase q h₂ y.1 y.2) (tubeMap x) t =
      lamAmb (basePhi q h₂ (tubeMap x).1 (tubeMap x).2)
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) 𝓘(ℝ, Ambient (q + 3))
          (BranchSmall.vectorTransfer q h₂ (transferHeight h₂)) (tubeMap x) t) -
        canonPrim q (tubeMap x) t)
    (v w : (ℝ × ℝ) × Fibre (q + 3)) :
    coupledForm (chartLiftExplicit q h₁ h₂ (Prod.map id unmix x))
      (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, E (q + 4))
        (fun x => chartLiftExplicit q h₁ h₂ (Prod.map id unmix x)) x v)
      (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, E (q + 4))
        (fun x => chartLiftExplicit q h₁ h₂ (Prod.map id unmix x)) x w) =
      mixedRHS x v w := by
  set y := tubeMap x with hydef
  set R := fun x : Surface q × Fibre (q + 3) => chartLiftExplicit q h₁ h₂ (Prod.map id unmix x)
    with hRdef
  set DR := mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, E (q + 4)) R x with hDR
  set DT := mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) tubeMap x
    with hDT
  set Ψf := fun y : Surface q × Fibre (q + 2) => liftPhase q h₂ y.1 y.2 with hΨf
  set φf := BranchSmall.vectorTransfer q h₂ (transferHeight h₂) with hφf
  set DΨ := mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) 𝓘(ℝ, ℝ) Ψf y with hDΨ
  set Dφ := mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) 𝓘(ℝ, Ambient (q + 3)) φf y with hDφ
  have hb1 : h₂ < transferHeight h₂ := by unfold transferHeight; linarith
  have hb2 : transferHeight h₂ < 1 / 2 := by unfold transferHeight; linarith
  have hspec := BranchSmall.vectorTransfer_spec q hh hb1 hb2
  have hφ : MDifferentiableAt 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) 𝓘(ℝ, Ambient (q + 3)) φf y :=
    ((hspec.1 y hy).contMDiffAt
      ((BranchSmall.transferDomain_isOpen q _).mem_nhds hy)).mdifferentiableAt (by simp)
  have hTd := hT.hasMFDerivAt
  have hΨc : HasMFDerivAt 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, ℝ)
      (fun x => Ψf (tubeMap x)) x (DΨ.comp DT) := hΨ.hasMFDerivAt.comp x hTd
  have hφc : HasMFDerivAt 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, Ambient (q + 3))
      (fun x => φf (tubeMap x)) x (Dφ.comp DT) :=
    HasMFDerivAt.comp (g := φf) (f := tubeMap) x hφ.hasMFDerivAt hTd
  -- the phase factor
  set E0 := Complex.exp (2 * Real.pi * Complex.I * (Ψf y : ℂ)) with hE0
  have hexp : HasDerivAt (fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))
      (E0 * (2 * Real.pi * Complex.I * 1)) (Ψf y) :=
    ((hasDerivAt_id (Ψf y)).ofReal_comp.const_mul (2 * Real.pi * Complex.I)).cexp
  have he : HasMFDerivAt 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, ℂ)
      (fun x => Complex.exp (2 * Real.pi * Complex.I * (Ψf (tubeMap x) : ℂ))) x
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (E0 * (2 * Real.pi * Complex.I * 1))).comp
        (DΨ.comp DT)) :=
    HasMFDerivAt.comp (g := fun t : ℝ => Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)))
      (f := fun x => Ψf (tubeMap x)) x hexp.hasFDerivAt.hasMFDerivAt hΨc
  have hg : HasMFDerivAt 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, ℂ)
      (fun x : Surface q × Fibre (q + 3) => planeC (x.2 0)) x
      ((Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (q + 3) => ℝ × ℝ) 0).comp
          (ContinuousLinearMap.snd ℝ (ℝ × ℝ) (Fibre (q + 3))))) := by
    have h := (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ).hasFDerivAt.hasMFDerivAt.comp x
      (hasMFDerivAt_fib0 x)
    have hfun : (fun x : Surface q × Fibre (q + 3) => planeC (x.2 0)) =
        (Complex.equivRealProdCLM.symm : ℝ × ℝ →L[ℝ] ℂ) ∘ (fun x => x.2 0) := by
      funext x; simp [planeC_eq_symm]
    rw [hfun]; exact h
  have hprod := he.mul hg
  set a : (ℝ × ℝ) × Fibre (q + 3) → ℝ := fun t => DΨ (DT t) with ha
  -- component `0`
  have hR0 : HasMFDerivAt 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, ℂ)
      (fun x => zc (R x) 0) x ((zcCLM 0).comp DR) :=
    (zcCLM (0 : Fin (q + 4))).hasFDerivAt.hasMFDerivAt.comp x hR.hasMFDerivAt
  have hfun0 : (fun x => zc (R x) 0) =
      (fun x => Complex.exp (2 * Real.pi * Complex.I * (Ψf (tubeMap x) : ℂ))) *
        (fun x : Surface q × Fibre (q + 3) => planeC (x.2 0)) := by
    funext x
    simp [hRdef, chartLiftExplicit, zc_ofPhase, Fin.cons_zero, unmix_zero, hΨf, tubeMap]
  rw [hfun0] at hR0
  have hD0 := hR0.mfderiv.symm.trans hprod.mfderiv
  -- components `i.succ`
  have hDs : ∀ i : Fin (q + 3), ∀ t : (ℝ × ℝ) × Fibre (q + 3),
      zc (DR t) i.succ = Dφ (DT t) i := by
    intro i t
    have hRi : HasMFDerivAt 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, ℂ)
        (fun x => zc (R x) i.succ) x ((zcCLM i.succ).comp DR) :=
      (zcCLM i.succ).hasFDerivAt.hasMFDerivAt.comp x hR.hasMFDerivAt
    have hfi : (fun x => zc (R x) i.succ) =
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (q + 3) => ℂ) i) ∘
          (fun x => φf (tubeMap x)) := by
      funext x
      simp only [hRdef, zc_succ_chartLiftExplicit, Function.comp, hφf, basePhi, tubeMap,
        Prod.map_fst, Prod.map_snd, id]
      rfl
    rw [hfi] at hRi
    have hi := HasMFDerivAt.comp (g := ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (q + 3) => ℂ) i) (f := fun x => φf (tubeMap x)) x
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (q + 3) => ℂ) i).hasFDerivAt.hasMFDerivAt
      hφc
    have := congrArg (fun L => L t) (hRi.mfderiv.symm.trans hi.mfderiv)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, zcCLM_apply] at this
    exact this
  have hD0t : ∀ t : (ℝ × ℝ) × Fibre (q + 3), zc (DR t) 0 =
      E0 * (planeC (t.2 0) + planeC (x.2 0) *
        (((a t : ℝ) : ℂ) * (2 * Real.pi * Complex.I))) := by
    intro t
    have := congrArg (fun L : ((ℝ × ℝ) × Fibre (q + 3)) →L[ℝ] ℂ => L t) hD0
    refine this.trans ?_
    change E0 * Complex.equivRealProdCLM.symm (t.2 0) +
        planeC (x.2 0) * (a t • (E0 * (2 * Real.pi * Complex.I * 1))) = _
    rw [← planeC_eq_symm, Complex.real_smul]
    ring
  -- values at `x`
  have hRx0 : zc (R x) 0 = E0 * planeC (x.2 0) := by
    simp [hRdef, chartLiftExplicit, zc_ofPhase, Fin.cons_zero, unmix_zero, hE0, hΨf, hydef,
      tubeMap]
  have hRxs : ∀ i : Fin (q + 3), zc (R x) i.succ = φf y i := by
    intro i
    simp only [hRdef, zc_succ_chartLiftExplicit, hφf, basePhi, hydef, tubeMap, Prod.map_fst,
      Prod.map_snd, id]
  have hEn : Complex.normSq E0 = 1 := normSq_exp_turn _
  -- the base parts
  have hbase : omegaBase (DR v) (DR w) = BranchSmall.quadricForm q y (DT v) (DT w) := by
    have h := hspec.2.2.1 y hy (DT v) (DT w)
    calc omegaBase (DR v) (DR w) =
        OAI.PackingSufficiencySupport.standardForm (Dφ (DT v)) (Dφ (DT w)) := by
          simp only [omegaBase, hDs]; rfl
      _ = successorStandardForm (q + 2) (Dφ (DT v)) (Dφ (DT w)) :=
          (successorStandardForm_apply _ _ _).symm
      _ = _ := h
  have hlam : ∀ t : (ℝ × ℝ) × Fibre (q + 3),
      lamBase (R x) (DR t) = lamAmb (φf y) (Dφ (DT t)) := by
    intro t
    simp only [lamBase, omegaBase, hDs, hRxs, lamAmb]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    ring
  have hfib : fibMoment (R x) = uMom x.2 := by
    show Real.pi * Complex.normSq (zc (R x) 0) = Real.pi * ((x.2 0).1 ^ 2 + (x.2 0).2 ^ 2)
    rw [hRx0, map_mul, hEn, one_mul]
    simp [planeC, Complex.normSq_apply]
    ring
  have hdF : ∀ t : (ℝ × ℝ) × Fibre (q + 3), dFib (R x) (DR t) = dUMom x.2 t.2 := by
    intro t
    have h := dot_mul_rot (X := planeC (x.2 0))
      (Y := planeC (t.2 0) + planeC (x.2 0) *
        (((a t : ℝ) : ℂ) * (2 * Real.pi * Complex.I))) hEn
    simp only [dFib, dUMom]
    rw [hRx0, hD0t t, h, rotX_re, rotX_im]
    simp only [planeC]
    ring
  have hωf : omegaFib (DR v) (DR w) =
      planeArea0 v.2 w.2 + a w * dUMom x.2 v.2 -
        a v * dUMom x.2 w.2 := by
    have h := cross_mul_rot
      (X := planeC (v.2 0) + planeC (x.2 0) * (((a v : ℝ) : ℂ) * (2 * Real.pi * Complex.I)))
      (Y := planeC (w.2 0) + planeC (x.2 0) * (((a w : ℝ) : ℂ) * (2 * Real.pi * Complex.I)))
      hEn
    simp only [omegaFib]
    rw [hD0t v, hD0t w, h, rotX_re, rotX_im, rotX_re, rotX_im]
    simp only [planeArea0, dUMom]
    ring
  -- assemble
  have hPv := hP (DT v)
  have hPw := hP (DT w)
  show omegaFib (DR v) (DR w) + (1 - fibMoment (R x)) * omegaBase (DR v) (DR w) -
      dFib (R x) (DR v) * lamBase (R x) (DR w) + dFib (R x) (DR w) * lamBase (R x) (DR v) = _
  rw [hωf, hbase, hfib, hdF, hdF, hlam, hlam]
  simp only [mixedRHS]
  change _ = planeArea0 v.2 w.2 + (1 - uMom x.2) * BranchSmall.quadricForm q y (DT v) (DT w) -
    dUMom x.2 v.2 * canonPrim q y (DT w) + dUMom x.2 w.2 * canonPrim q y (DT v)
  have e1 : a v = lamAmb (φf y) (Dφ (DT v)) - canonPrim q y (DT v) := hPv
  have e2 : a w = lamAmb (φf y) (Dφ (DT w)) - canonPrim q y (DT w) := hPw
  rw [e1, e2]
  ring

/-- **`lem:two-identification` (iv),(v)**: on the transfer tube the lift phase is a primitive of
`φ^*λ_base − ℓ`. (Radial Poincaré lemma for the closed form `φ^*λ_base − ℓ`, `d(φ^*λ_base) =
φ^*ω₀ = Ω_X = dℓ`, along the star-shaped fibres, with `ℓ(0, w) = 0` on radial vectors; over the
zero section the transfer paths are constant (`lem:two-zero-fixed`), so `zeroPhase = 0`, and
`ι^*λ_base = curveFSPrimitive (1/π)` because the ball chart pulls `λ_base` back to
`affineFSPrimitive (1/π)`.) -/
theorem liftPhase_mfderiv (q : ℕ) {h₂ : ℝ} (hh : 0 < h₂) (hh2 : h₂ < 1 / 2)
    (y : Surface q × Fibre (q + 2)) (hy : y ∈ BranchSmall.transferDomain q (transferHeight h₂))
    (t : (ℝ × ℝ) × Fibre (q + 2)) :
    mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) 𝓘(ℝ, ℝ)
        (fun y : Surface q × Fibre (q + 2) => liftPhase q h₂ y.1 y.2) y t =
      lamAmb (basePhi q h₂ y.1 y.2)
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) 𝓘(ℝ, Ambient (q + 3))
          (BranchSmall.vectorTransfer q h₂ (transferHeight h₂)) y t) -
        canonPrim q y t := by
  have h := liftPhase_differential hh hh2 y hy t
  rw [normalCouplingPrimitive_canonPrim] at h
  exact h

/-- **`lem:two-mixed` (ii)**: in mixed coordinates `p_j = (1 − u) v_j` the mixed model form is
`Ω_mix = ω_fib + (1 − u) T^*Ω_X − du ∧ T^*ℓ` on `u < 1`
(`(1−u) dv_j = dp_j + v_j du`, `(1−u)(1 − 2Σv) = 1 − u − 2w`). -/
theorem mixedModel_form_eq {q : ℕ} (a : ℝ) (rr : Fin k → ℝ) (x : Surface q × Fibre (q + 3))
    (hu : uMom x.2 < 1) (v w : (ℝ × ℝ) × Fibre (q + 3)) :
    (mixedModel q a rr).form x v w = mixedRHS x v w := by
  let A := parameters q
  let U : Set (Fibre (q + 3)) := {ζ | uMom ζ < 1}
  let σ : Fibre (q + 3) → ℝ := fun ζ => (Real.sqrt (1 - uMom ζ))⁻¹
  have hU : IsOpen U := isOpen_lt
    (radialArea_smooth.continuous.comp (continuous_apply 0)) continuous_const
  have hσ : ContDiffOn ℝ ∞ σ U := by
    apply ContDiffOn.inv
    · apply ContDiffOn.sqrt
      · exact (contDiff_const.sub (radialArea_smooth.comp (contDiff_apply ℝ _ 0))).contDiffOn
      · intro ζ hζ
        exact (sub_pos.mpr (show uMom ζ < 1 from hζ)).ne'
    · intro ζ hζ
      exact (Real.sqrt_pos.mpr (sub_pos.mpr (show uMom ζ < 1 from hζ))).ne'
  obtain ⟨χ, _, _, _, _, _, hs, _, hse⟩ := exists_smooth_compact_extension
    (isCompact_singleton : IsCompact {x.2}) hU (singleton_subset_iff.mpr hu) hσ
  let s : Fibre (q + 3) → ℝ := fun ζ => χ ζ * σ ζ
  have hs : ContDiff ℝ ∞ s := hs
  obtain ⟨O, hO, hxO, hOs⟩ := mem_nhdsSet_iff_exists.mp hse
  have hxO : x.2 ∈ O := hxO (mem_singleton _)
  let V : Set (Surface q × Fibre (q + 3)) := Prod.snd ⁻¹' (O ∩ U)
  have hV : IsOpen V := (hO.inter hU).preimage continuous_snd
  have hxV : x ∈ V := ⟨hxO, hu⟩
  have hratio : ∀ y ∈ V, (1 - radialArea (normalHead (q + 2) y.2)) * (s y.2) ^ 2 = 1 := by
    intro y hy
    have hsy : s y.2 = σ y.2 := hOs hy.1
    have hpos : 0 < 1 - uMom y.2 := sub_pos.mpr hy.2
    rw [hsy]
    change (1 - uMom y.2) * ((Real.sqrt (1 - uMom y.2))⁻¹) ^ 2 = 1
    rw [inv_pow, Real.sq_sqrt hpos.le, mul_inv_cancel₀ hpos.ne']
  let F := firstTailMap s (M := Surface q)
  have hF : ContMDiff 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3))
      𝓘(ℝ, ((ℝ × ℝ) × Fibre (q + 2)) × Plane) ∞ F := firstTailMap_smooth hs
  have hprim : manifoldPullbackOneForm (fun _ : ℝ => firstLinePrimitive (normalCouplingPrimitive A)) F 0
      =ᶠ[𝓝 x] largeCouplingPrimitive A := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    exact firstTailMap_primitive A hs y (hratio y hy)
  have htube : (Prod.fst ∘ F) =ᶠ[𝓝 x] tubeMap (q := q) := by
    filter_upwards [hV.mem_nhds hxV] with y hy
    apply Prod.ext
    · rfl
    · funext j
      have hsj : (j.succ : Fin (q + 3)) ≠ 0 := Fin.succ_ne_zero j
      change s y.2 • y.2 j.succ = tailFibre (unmix y.2) j
      have hsy : s y.2 = σ y.2 := hOs hy.1
      rw [hsy]
      simp only [tailFibre, unmix, if_neg hsj, σ]
  have hFfst (t : (ℝ × ℝ) × Fibre (q + 3)) :
      (manifoldMapDifferential (E := ((ℝ × ℝ) × Fibre (q + 2)) × Plane)
        (F := (ℝ × ℝ) × Fibre (q + 3)) F x t).1 =
      mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3))
        𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) tubeMap x t := by
    have hd := mfderiv_comp x ((flatProduct_fst_smooth (E := (ℝ × ℝ) × Fibre (q + 2))
      (M := Surface q × Fibre (q + 2)) (V := Plane)).mdifferentiable (by simp) (F x))
      (hF.mdifferentiable (by simp) x)
    rw [htube.mfderiv_eq, flatProduct_fst_derivative] at hd
    exact congrArg (fun L => L t) hd.symm
  have hFsnd (t : (ℝ × ℝ) × Fibre (q + 3)) :
      (manifoldMapDifferential (E := ((ℝ × ℝ) × Fibre (q + 2)) × Plane)
        (F := (ℝ × ℝ) × Fibre (q + 3)) F x t).2 = t.2 0 := by
    change (manifoldMapDifferential (E := ((ℝ × ℝ) × Fibre (q + 2)) × Plane)
      (F := (ℝ × ℝ) × Fibre (q + 3)) (firstTailMap s) x t).2 = _
    rw [firstTailMap_derivative hs]
    rfl
  have hcanon := normalCouplingPrimitive_canonPrim q
  have hext := manifold_pullback_exterior
    (fun c y hy => ((firstLinePrimitive_family_smooth (normalCouplingPrimitive_smooth A)).spatial_smooth
      0 c hy).contDiffWithinAt) hF x
  rw [manifoldExteriorOneForm_congr_germ hprim] at hext
  have hext' : manifoldExteriorOneForm (largeCouplingPrimitive A) x v w =
      manifoldExteriorOneForm (firstLinePrimitive (normalCouplingPrimitive A)) (F x)
        (manifoldMapDifferential (E := ((ℝ × ℝ) × Fibre (q + 2)) × Plane)
          (F := (ℝ × ℝ) × Fibre (q + 3)) F x v)
        (manifoldMapDifferential (E := ((ℝ × ℝ) × Fibre (q + 2)) × Plane)
          (F := (ℝ × ℝ) × Fibre (q + 3)) F x w) := by
    convert! congrArg (fun L => L v w) hext using 1
  rw [firstLine_exterior (normalCouplingPrimitive_smooth A)] at hext'
  simp only [hFfst, hFsnd] at hext'
  rw [show (F x).1 = tubeMap x from htube.eq_of_nhds,
    show (F x).2 = x.2 0 from rfl, normalCouplingPrimitive_exterior] at hext'
  have hcv := hcanon (tubeMap x)
    (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) tubeMap x v)
  have hcw := hcanon (tubeMap x)
    (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 3)) 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) tubeMap x w)
  rw [hcv, hcw] at hext'
  simp only [radialArea_fderiv] at hext' 
  rw [largeCouplingPrimitive_exterior] at hext'
  change (mixedModel q a rr).form x v w = _ at hext'
  simpa only [mixedRHS, planeArea0, uMom, dUMom, BranchSmall.quadricForm, A, planarArea_apply] using hext'



end SymplecticPacking.BranchLargeHigh.Two
