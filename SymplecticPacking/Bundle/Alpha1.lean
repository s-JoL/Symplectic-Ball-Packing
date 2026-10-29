import SymplecticPacking.Bundle.Pprim

/-!
# The annular primitive and the global primitive `α₁`

`sec:fer` (`def:fer-Delta`, `def:fer-FA`, `cons:fer-alpha1`): smoothness predicates for
coefficients (`Smooth`, `SmoothOn`), the band `𝒜⁺ × ℝ` (`bandSet`), and the definitions of the
annular difference `Δ` (`DeltaA`), its core period `c(p)` (`corePeriod`), the annular primitive
`F_𝒜` (`FA`, `zetaFA`) and the global primitive `α₁` (`alpha1`), obtained from `alpha1pre` by
subtracting the jets `Ajet`, `Bjet` at the three points `b_j`.

`Δ`, `F_𝒜` are defined by their formulas on all of `ℝ³` but only used (and only meaningful) on
the band `𝒜⁺ × ℝ` (`bandSet`), where `Z₀ ≠ 0`. `ζ_𝒜 F_𝒜` is extended by zero via `Int.fract`.
-/

noncomputable section

namespace SymplecticPacking.Bundle

open Set Filter Topology MeasureTheory
open scoped ContDiff Real

attribute [local irreducible] lambdaCu lambdaCv sigmaC etaHu etaHv

/-! ### Generic base-form calculus -/

namespace BForm

/-- Smoothness of both coefficient slices at fixed `p`. -/
def Smooth (α : BForm) (p : ℝ) : Prop :=
  ContDiff ℝ ∞ (sl α.cu p) ∧ ContDiff ℝ ∞ (sl α.cv p)

/-- Smoothness of both coefficient slices on a set. -/
def SmoothOn (α : BForm) (p : ℝ) (O : Set (ℝ × ℝ)) : Prop :=
  ContDiffOn ℝ ∞ (sl α.cu p) O ∧ ContDiffOn ℝ ∞ (sl α.cv p) O

lemma Smooth.smoothOn {α : BForm} {p : ℝ} (h : α.Smooth p) (O : Set (ℝ × ℝ)) : α.SmoothOn p O :=
  ⟨h.1.contDiffOn, h.2.contDiffOn⟩

lemma Smooth.sub {α β : BForm} {p : ℝ} (hα : α.Smooth p) (hβ : β.Smooth p) :
    (α - β).Smooth p := ⟨hα.1.sub hβ.1, hα.2.sub hβ.2⟩

lemma SmoothOn.add {α β : BForm} {p : ℝ} {O : Set (ℝ × ℝ)} (hα : α.SmoothOn p O)
    (hβ : β.SmoothOn p O) : (α + β).SmoothOn p O := ⟨hα.1.add hβ.1, hα.2.add hβ.2⟩

lemma SmoothOn.sub {α β : BForm} {p : ℝ} {O : Set (ℝ × ℝ)} (hα : α.SmoothOn p O)
    (hβ : β.SmoothOn p O) : (α - β).SmoothOn p O := ⟨hα.1.sub hβ.1, hα.2.sub hβ.2⟩

lemma SmoothOn.pmul {α : BForm} {p : ℝ} {O : Set (ℝ × ℝ)} (c : ℝ → ℝ) (hα : α.SmoothOn p O) :
    (pmul c α).SmoothOn p O := ⟨contDiffOn_const.mul hα.1, contDiffOn_const.mul hα.2⟩

lemma SmoothOn.diffAt {α : BForm} {p : ℝ} {O : Set (ℝ × ℝ)} (h : α.SmoothOn p O) (hO : IsOpen O)
    {x : ℝ × ℝ} (hx : x ∈ O) :
    DifferentiableAt ℝ (sl α.cu p) x ∧ DifferentiableAt ℝ (sl α.cv p) x :=
  ⟨(h.1.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp),
    (h.2.contDiffAt (hO.mem_nhds hx)).differentiableAt (by simp)⟩

lemma dC_add {α β : BForm} {u v p : ℝ}
    (hα : DifferentiableAt ℝ (sl α.cu p) (u, v) ∧ DifferentiableAt ℝ (sl α.cv p) (u, v))
    (hβ : DifferentiableAt ℝ (sl β.cu p) (u, v) ∧ DifferentiableAt ℝ (sl β.cv p) (u, v)) :
    (α + β).dC u v p = α.dC u v p + β.dC u v p := by
  simp only [dC, add_cu, add_cv, Bundle.pu, Bundle.pv, Pi.add_apply]
  have e1 : deriv (fun s => α.cv s v p + β.cv s v p) u = pu α.cv u v p + pu β.cv u v p :=
    ((hasDerivAt_pu hα.2).add (hasDerivAt_pu hβ.2)).deriv
  have e2 : deriv (fun t => α.cu u t p + β.cu u t p) v = pv α.cu u v p + pv β.cu u v p :=
    ((hasDerivAt_pv hα.1).add (hasDerivAt_pv hβ.1)).deriv
  rw [e1, e2]; simp only [Bundle.pu, Bundle.pv]; ring

lemma dC_sub {α β : BForm} {u v p : ℝ}
    (hα : DifferentiableAt ℝ (sl α.cu p) (u, v) ∧ DifferentiableAt ℝ (sl α.cv p) (u, v))
    (hβ : DifferentiableAt ℝ (sl β.cu p) (u, v) ∧ DifferentiableAt ℝ (sl β.cv p) (u, v)) :
    (α - β).dC u v p = α.dC u v p - β.dC u v p := by
  simp only [dC, sub_cu, sub_cv, Bundle.pu, Bundle.pv, Pi.sub_apply]
  have e1 : deriv (fun s => α.cv s v p - β.cv s v p) u = pu α.cv u v p - pu β.cv u v p :=
    ((hasDerivAt_pu hα.2).sub (hasDerivAt_pu hβ.2)).deriv
  have e2 : deriv (fun t => α.cu u t p - β.cu u t p) v = pv α.cu u v p - pv β.cu u v p :=
    ((hasDerivAt_pv hα.1).sub (hasDerivAt_pv hβ.1)).deriv
  rw [e1, e2]; simp only [Bundle.pu, Bundle.pv]; ring

lemma dC_pmul (c : ℝ → ℝ) (α : BForm) (u v p : ℝ) :
    (pmul c α).dC u v p = c p * α.dC u v p := by
  simp only [dC, pmul, Bundle.pu, Bundle.pv, deriv_const_mul_field]; ring

end BForm

lemma smooth_dCf {F : Coef} {p : ℝ} (h : ContDiff ℝ ∞ (sl F p)) : (dCf F).Smooth p := by
  constructor
  · rw [contDiff_iff_contDiffAt]; exact fun x => contDiffAt_pu_infty h.contDiffAt
  · rw [contDiff_iff_contDiffAt]; exact fun x => contDiffAt_pv_infty h.contDiffAt

lemma dC_dCf_of_smooth {F : Coef} {p : ℝ} (h : ContDiff ℝ ∞ (sl F p)) (u v : ℝ) :
    (dCf F).dC u v p = 0 := dC_dCf (h.contDiffAt.of_le (by simp))

/-- Partial derivatives only depend on the germ of the slice. -/
lemma pu_congr {f g : Coef} {u v p : ℝ} (h : sl f p =ᶠ[𝓝 (u, v)] sl g p) :
    pu f u v p = pu g u v p := by
  simp only [pu]
  apply Filter.EventuallyEq.deriv_eq
  have := ((continuous_id.prodMk (continuous_const (y := v))).tendsto u).eventually h
  exact this

lemma pv_congr {f g : Coef} {u v p : ℝ} (h : sl f p =ᶠ[𝓝 (u, v)] sl g p) :
    pv f u v p = pv g u v p := by
  simp only [pv]
  apply Filter.EventuallyEq.deriv_eq
  have := (((continuous_const (y := u)).prodMk continuous_id).tendsto v).eventually h
  exact this

lemma pu_congr' {f g : Coef} {x : ℝ × ℝ} {p : ℝ} (h : sl f p =ᶠ[𝓝 x] sl g p) :
    pu f x.1 x.2 p = pu g x.1 x.2 p := pu_congr h

lemma pv_congr' {f g : Coef} {x : ℝ × ℝ} {p : ℝ} (h : sl f p =ᶠ[𝓝 x] sl g p) :
    pv f x.1 x.2 p = pv g x.1 x.2 p := pv_congr h

lemma pu_periodic {f : Coef} (hf : CoefPeriodic f) (u v p : ℝ) :
    pu f (u + 1) v p = pu f u v p ∧ pu f u (v + 1) p = pu f u v p := by
  constructor
  · simp only [pu]
    rw [← deriv_comp_add_const]
    simp only [(hf _ v p).1]
  · simp only [pu, (hf _ v p).2]

lemma pv_periodic {f : Coef} (hf : CoefPeriodic f) (u v p : ℝ) :
    pv f (u + 1) v p = pv f u v p ∧ pv f u (v + 1) p = pv f u v p := by
  constructor
  · simp only [pv, (hf u _ p).1]
  · simp only [pv]
    rw [← deriv_comp_add_const]
    simp only [(hf u _ p).2]

/-- FTC on an open interval where the integrand is continuous. -/
lemma hasDerivAt_integral_Ioo {g : ℝ → ℝ} {α β a s : ℝ} (hg : ContinuousOn g (Ioo α β))
    (ha : a ∈ Ioo α β) (hs : s ∈ Ioo α β) :
    HasDerivAt (fun x => ∫ t in a..x, g t) (g s) s := by
  have hsub : uIcc a s ⊆ Ioo α β := (ordConnected_Ioo).uIcc_subset ha hs
  exact intervalIntegral.integral_hasDerivAt_right ((hg.mono hsub).intervalIntegrable)
    (hg.stronglyMeasurableAtFilter isOpen_Ioo s hs)
    (hg.continuousAt (isOpen_Ioo.mem_nhds hs))

/-- Smoothness of `s ↦ ∫ₐˢ g` on an open interval where `g` is smooth. -/
lemma contDiffOn_integral_Ioo {g : ℝ → ℝ} {α β a : ℝ} (hg : ContDiffOn ℝ ∞ g (Ioo α β))
    (ha : a ∈ Ioo α β) : ContDiffOn ℝ ∞ (fun x => ∫ t in a..x, g t) (Ioo α β) := by
  have hd : ∀ s ∈ Ioo α β, HasDerivAt (fun x => ∫ t in a..x, g t) (g s) s := fun s hs =>
    hasDerivAt_integral_Ioo hg.continuousOn ha hs
  rw [contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨fun s hs => (hd s hs).differentiableAt.differentiableWithinAt, ?_⟩
  exact hg.congr fun s hs => (hd s hs).deriv

/-- Smoothness of `(s, v) ↦ ∫₀ᵛ g(s, w) dw` on `I × ℝ` for `g` smooth on `I × ℝ`, `I` open. -/
lemma contDiffOn_param_primitive {g : ℝ × ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hg : ContDiffOn ℝ ∞ g (I ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => ∫ w in (0 : ℝ)..x.2, g (x.1, w)) (I ×ˢ univ) := by
  intro x₀ hx₀
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hI x₀.1 hx₀.1
  let ρ : ContDiffBump x₀.1 := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hρs : tsupport ρ ⊆ I := by
    rw [ρ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (show r / 2 < r by linarith)).trans hball
  -- the cut-off integrand is smooth everywhere
  have hG : ContDiff ℝ ∞ (fun y : ℝ × ℝ => ρ y.1 * g y) := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y.1 ∈ I
    · exact (ρ.contDiff.comp contDiff_fst).contDiffAt.mul
        (hg.contDiffAt ((hI.prod isOpen_univ).mem_nhds ⟨hy, mem_univ _⟩))
    · have hy' : y.1 ∉ tsupport ρ := fun h => hy (hρs h)
      have hev : (fun y : ℝ × ℝ => ρ y.1 * g y) =ᶠ[𝓝 y] fun _ => 0 := by
        have := (continuous_fst.tendsto y).eventually
          ((notMem_tsupport_iff_eventuallyEq (f := ρ) (x := y.1)).mp hy')
        filter_upwards [this] with z hz
        simp [hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hP := contDiff_primitive (P := ℝ × ℝ) (g := fun q : ℝ × (ℝ × ℝ) => ρ q.2.1 * g (q.2.1, q.1))
    (hG.comp (contDiff_snd.fst.prodMk contDiff_fst)) (s := fun x => x.2) contDiff_snd
  refine hP.contDiffAt.congr_of_eventuallyEq ?_
  have hn : Metric.ball x₀.1 (r / 4) ∈ 𝓝 x₀.1 := Metric.ball_mem_nhds _ (by positivity)
  filter_upwards [(continuous_fst.tendsto x₀).eventually hn] with x hx
  refine intervalIntegral.integral_congr fun w _ => ?_
  rw [ρ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx), one_mul]

/-! ### The band `𝒜⁺ × ℝ` -/

/-- The band `𝒜⁺ × ℝ` in the fundamental strip. -/
def bandSet : Set (ℝ × ℝ) := annulusPlus ×ˢ univ

lemma isOpen_bandSet : IsOpen bandSet := isOpen_Ioo.prod isOpen_univ

lemma bandSet_subset : bandSet ⊆ ZnzSet := fun x hx => Zunit_zero_ne_zero_of_mem hx.1 x.2

/-! ### The annular difference `Δ` (`def:fer-Delta`) -/

/-- `a_𝒜 = −3λ_C`. -/
def aA : BForm := BForm.pmul (fun _ => -3) lambdaC

/-- `γ_sm = e_h (u − 1/6) dv`. -/
def gammaSm (P : Params) : BForm := ⟨fun _ _ _ => 0, fun u _ _ => P.eh * (u - 1 / 6)⟩

/-- `f(s) H*(p) β`. -/
def fHbeta (P : Params) : BForm := ⟨fun _ _ _ => 0, fun u v p => stepA u * P.Hstar p * bB v⟩

/-- **`Δ = γ_σ + p a_𝒜 + α₁⁰ − γ_sm − f H* β`** (with `γ_σ = λ_C`). -/
def DeltaA (P : Params) : BForm :=
  lambdaC + BForm.pmul (fun p => p) aA + alpha10 P - gammaSm P - fHbeta P

lemma DeltaA_cu (P : Params) (u v p : ℝ) :
    (DeltaA P).cu u v p = (1 - 3 * p) * lambdaCu u v + (alpha10 P).cu u v p := by
  simp only [DeltaA, BForm.sub_cu, BForm.add_cu, BForm.pmul, aA, lambdaC, gammaSm, fHbeta, ofUV,
    Pi.add_apply, Pi.sub_apply]
  ring

lemma DeltaA_cv (P : Params) (u v p : ℝ) :
    (DeltaA P).cv u v p = (1 - 3 * p) * lambdaCv u v + (alpha10 P).cv u v p -
      P.eh * (u - 1 / 6) - stepA u * P.Hstar p * bB v := by
  simp only [DeltaA, BForm.sub_cv, BForm.add_cv, BForm.pmul, aA, lambdaC, gammaSm, fHbeta, ofUV,
    Pi.add_apply, Pi.sub_apply]
  ring

lemma smoothOn_lambdaC (p : ℝ) : lambdaC.SmoothOn p bandSet :=
  ⟨contDiffOn_lambdaCu.mono bandSet_subset, contDiffOn_lambdaCv.mono bandSet_subset⟩

lemma smooth_alpha10 (P : Params) (p : ℝ) : (alpha10 P).Smooth p :=
  ⟨contDiff_Pprim_cu (contDiff_kdiff P p), contDiff_Pprim_cv (contDiff_kdiff P p)⟩

lemma smooth_gammaSm (P : Params) (p : ℝ) : (gammaSm P).Smooth p :=
  ⟨contDiff_const, contDiff_const.mul (contDiff_fst.sub contDiff_const)⟩

lemma smooth_fHbeta (P : Params) (p : ℝ) : (fHbeta P).Smooth p :=
  ⟨contDiff_const, ((contDiff_stepA.comp contDiff_fst).mul contDiff_const).mul
    (contDiff_bB.comp contDiff_snd)⟩

lemma smoothOn_DeltaA (P : Params) (p : ℝ) : (DeltaA P).SmoothOn p bandSet :=
  ((((smoothOn_lambdaC p).add ((smoothOn_lambdaC p).pmul (fun _ => -3) |>.pmul (fun p => p))).add
    ((smooth_alpha10 P p).smoothOn _)).sub ((smooth_gammaSm P p).smoothOn _)).sub
    ((smooth_fHbeta P p).smoothOn _)

lemma dC_lambdaC_band {u v p : ℝ} (hu : u ∈ annulusPlus) : lambdaC.dC u v p = sigmaC u v :=
  d_lambdaC (Zunit_zero_ne_zero_of_mem hu v) p

lemma chiA_band {u v : ℝ} (hu : u ∈ annulusPlus) : chiA u v = deriv stepA u * bB v := by
  rw [chiA, fract_of_mem_Ico ⟨by linarith [hu.1], by linarith [hu.2]⟩]

/-! ### Periodicity of `Δ` in `v` on the band -/

/-! ### The core period (`def:fer-Delta`, `lem:fer-Delta`) -/

/-- **The core period** `c(p) = ∮_{u = 1/6} Δ`. -/
def corePeriod (P : Params) (p : ℝ) : ℝ := ∫ w in (0 : ℝ)..1, (DeltaA P).cv (1 / 6) w p

lemma one_sixth_mem : (1 / 6 : ℝ) ∈ annulusPlus := ⟨by norm_num, by norm_num⟩

lemma DeltaA_smoothAt (P : Params) {u : ℝ} (hu : u ∈ annulusPlus) (v p : ℝ) :
    ContDiffAt ℝ ∞ (sl (DeltaA P).cu p) (u, v) ∧ ContDiffAt ℝ ∞ (sl (DeltaA P).cv p) (u, v) :=
  ⟨(smoothOn_DeltaA P p).1.contDiffAt (isOpen_bandSet.mem_nhds ⟨hu, mem_univ _⟩),
    (smoothOn_DeltaA P p).2.contDiffAt (isOpen_bandSet.mem_nhds ⟨hu, mem_univ _⟩)⟩

lemma continuous_DeltaA_cv_v (P : Params) {u : ℝ} (hu : u ∈ annulusPlus) (p : ℝ) :
    Continuous (fun w => (DeltaA P).cv u w p) :=
  continuous_iff_continuousAt.mpr fun w =>
    ((DeltaA_smoothAt P hu w p).2.continuousAt.comp
      ((continuous_const.prodMk continuous_id).continuousAt (x := w)) : _)

lemma DeltaA_affine (P : Params) : AffineP (DeltaA P).cu ∧ AffineP (DeltaA P).cv := by
  obtain ⟨h1, h2⟩ := alpha10_affine P
  constructor
  · intro u v p
    rw [DeltaA_cu, DeltaA_cu, DeltaA_cu, h1 u v p]; ring
  · intro u v p
    rw [DeltaA_cv, DeltaA_cv, DeltaA_cv, h2 u v p]
    simp only [Params.Hstar, Params.Hb]; ring

/-- **`c` is affine in `p`** (`lem:fer-Delta`). -/
theorem corePeriod_affine (P : Params) (p : ℝ) :
    corePeriod P p = corePeriod P 0 + p * (corePeriod P 1 - corePeriod P 0) :=
  integral_affine (g := fun w p => (DeltaA P).cv (1 / 6) w p)
    (fun w p => (DeltaA_affine P).2 (1 / 6) w p)
    ((continuous_DeltaA_cv_v P one_sixth_mem 0).intervalIntegrable _ _)
    ((continuous_DeltaA_cv_v P one_sixth_mem 1).intervalIntegrable _ _) p

attribute [local irreducible] DeltaA

lemma continuous_cb (c : ℝ) : Continuous (fun w => c * bB w) :=
  continuous_const.mul contDiff_bB.continuous

/-! ### The annular primitive `F_𝒜` (`def:fer-FA`, `lem:fer-FA`) -/

/-- **`F_𝒜(s, v, p) = ∫_{1/6}^s D_s(t, 0, p) dt + ∫₀^v D_v(s, w, p) dw`**, where
`Δ − c(p) β = D_s ds + D_v dv` (so `D_s = Δ_s`, `D_v = Δ_v − c(p) b(v)`). -/
def FA (P : Params) (s v p : ℝ) : ℝ :=
  (∫ t in (1 / 6 : ℝ)..s, (DeltaA P).cu t 0 p) +
    ∫ w in (0 : ℝ)..v, ((DeltaA P).cv s w p - corePeriod P p * bB w)

lemma continuousOn_DeltaA_cu_u (P : Params) (v p : ℝ) :
    ContinuousOn (fun t => (DeltaA P).cu t v p) annulusPlus := by
  have h : ContinuousOn (sl (DeltaA P).cu p) bandSet := (smoothOn_DeltaA P p).1.continuousOn
  exact h.comp (continuous_id.prodMk continuous_const).continuousOn fun t ht => ⟨ht, mem_univ _⟩

/-- `F_𝒜` is smooth on the band. -/
theorem contDiffOn_FA (P : Params) (p : ℝ) : ContDiffOn ℝ ∞ (sl (FA P) p) bandSet := by
  have h1 : ContDiffOn ℝ ∞ (fun t => (DeltaA P).cu t 0 p) annulusPlus :=
    (smoothOn_DeltaA P p).1.comp (contDiff_id.prodMk contDiff_const).contDiffOn
      fun t ht => ⟨ht, mem_univ _⟩
  have hT1 := (contDiffOn_integral_Ioo h1 one_sixth_mem).comp contDiff_fst.contDiffOn
    (s := bandSet) fun x hx => hx.1
  have hg : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => (DeltaA P).cv x.1 x.2 p - corePeriod P p * bB x.2)
      (annulusPlus ×ˢ univ) :=
    (smoothOn_DeltaA P p).2.sub (contDiffOn_const.mul (contDiff_bB.comp contDiff_snd).contDiffOn)
  have hT2 := contDiffOn_param_primitive isOpen_Ioo hg
  exact hT1.add hT2

lemma FA_affine (P : Params) {s : ℝ} (hs : s ∈ annulusPlus) (v p : ℝ) :
    FA P s v p = FA P s v 0 + p * (FA P s v 1 - FA P s v 0) := by
  have hc : ∀ q, ContinuousOn (fun t => (DeltaA P).cu t 0 q) (uIcc (1 / 6) s) := fun q =>
    (continuousOn_DeltaA_cu_u P 0 q).mono ((ordConnected_Ioo).uIcc_subset one_sixth_mem hs)
  have hd : ∀ q, Continuous (fun w => (DeltaA P).cv s w q - corePeriod P q * bB w) := fun q =>
    (continuous_DeltaA_cv_v P hs q).sub (continuous_cb _)
  have e1 := integral_affine (g := fun t q => (DeltaA P).cu t 0 q)
    (fun t q => (DeltaA_affine P).1 t 0 q) (hc 0).intervalIntegrable (hc 1).intervalIntegrable p
  have e2 := integral_affine (g := fun w q => (DeltaA P).cv s w q - corePeriod P q * bB w)
    (fun w q => by rw [(DeltaA_affine P).2 s w q, corePeriod_affine P q]; ring)
    ((hd 0).intervalIntegrable _ _) ((hd 1).intervalIntegrable _ _) p (a := 0) (b := v)
  simp only [FA]
  rw [e1, e2]; ring

/-! ### `ζ_𝒜 F_𝒜`, extended by zero -/

/-- `ζ_𝒜 F_𝒜`, extended by zero outside `𝒜⁺` (periodically in `u`). -/
def zetaFA (P : Params) (u v p : ℝ) : ℝ :=
  if 1 / 12 < Int.fract u ∧ Int.fract u < 1 / 4 then zetaA u * FA P (Int.fract u) v p else 0

lemma eventually_fract_notMem {u₀ a b : ℝ} (ha : 0 < a) (hb : b < 1)
    (h : Int.fract u₀ ∉ Icc a b) : ∀ᶠ u in 𝓝 u₀, Int.fract u ∉ Icc a b := by
  by_cases h0 : Int.fract u₀ = 0
  · have hδ : 0 < min a (1 - b) := lt_min ha (by linarith)
    filter_upwards [fract_eventually_near_int h0 hδ] with y hy hs'
    rcases hy with hs | hs
    · linarith [min_le_left a (1 - b), hs'.1]
    · linarith [min_le_right a (1 - b), hs'.2]
  · have hc : ContinuousAt (fun x => x - (⌊u₀⌋ : ℝ)) u₀ := (continuous_id.sub continuous_const).continuousAt
    have hopen : (Icc a b)ᶜ ∈ 𝓝 (u₀ - ⌊u₀⌋) := isClosed_Icc.isOpen_compl.mem_nhds (by
      rw [← Int.fract]; exact h)
    filter_upwards [fract_eventually_of_not_int h0, hc.preimage_mem_nhds hopen] with y hy hy'
    rw [hy]; exact hy'

lemma zetaFA_eq_zero {P : Params} {u : ℝ} (h : Int.fract u ∉ Icc (9 / 96 : ℝ) (23 / 96)) (v p : ℝ) :
    zetaFA P u v p = 0 := by
  have : zetaA u = 0 := zetaA_eq_zero fun h' => h (Ioo_subset_Icc_self h')
  simp [zetaFA, this]

/-- `ζ_𝒜 F_𝒜` is smooth on the whole cover. -/
theorem contDiff_zetaFA (P : Params) (p : ℝ) : ContDiff ℝ ∞ (sl (zetaFA P) p) := by
  rw [contDiff_iff_contDiffAt]
  intro x₀
  by_cases hx : 1 / 12 < Int.fract x₀.1 ∧ Int.fract x₀.1 < 1 / 4
  · have h0 : Int.fract x₀.1 ≠ 0 := by linarith [hx.1]
    obtain ⟨n, hn⟩ : ∃ n : ℝ, n = ((⌊x₀.1⌋ : ℤ) : ℝ) := ⟨_, rfl⟩
    have hev1 := (continuous_fst.tendsto x₀).eventually (fract_eventually_of_not_int h0)
    rw [← hn] at hev1
    have hmem : x₀.1 - n ∈ annulusPlus := by
      show x₀.1 - n ∈ Ioo _ _
      rw [show x₀.1 - n = Int.fract x₀.1 by rw [hn, Int.fract]]; exact hx
    have hev2 : ∀ᶠ x in 𝓝 x₀, x.1 - n ∈ annulusPlus :=
      ((continuous_fst.sub continuous_const).tendsto x₀).eventually (isOpen_Ioo.mem_nhds hmem)
    have hev : sl (zetaFA P) p =ᶠ[𝓝 x₀] fun x => zetaA0 (x.1 - n) * FA P (x.1 - n) x.2 p := by
      filter_upwards [hev1, hev2] with x hx1 hx2
      simp only [sl, zetaFA, zetaA, hx1]
      rw [if_pos (show 1 / 12 < x.1 - n ∧ x.1 - n < 1 / 4 from hx2)]
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    have hs : ContDiff ℝ ∞ (fun x : ℝ × ℝ => ((x.1 - n, x.2) : ℝ × ℝ)) :=
      (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
    refine (contDiff_zetaA0.comp (contDiff_fst.sub contDiff_const)).contDiffAt.mul ?_
    exact ((contDiffOn_FA P p).contDiffAt (isOpen_bandSet.mem_nhds ⟨hmem, mem_univ _⟩)).comp x₀
      hs.contDiffAt
  · have hx' : Int.fract x₀.1 ∉ Icc (9 / 96 : ℝ) (23 / 96) := fun h =>
      hx ⟨by linarith [h.1], by linarith [h.2]⟩
    have hev : sl (zetaFA P) p =ᶠ[𝓝 x₀] fun _ => 0 := by
      filter_upwards [(continuous_fst.tendsto x₀).eventually
        (eventually_fract_notMem (by norm_num) (by norm_num) hx')] with x hx
      exact zetaFA_eq_zero hx _ _
    exact contDiffAt_const.congr_of_eventuallyEq hev

lemma zetaFA_affine (P : Params) : AffineP (zetaFA P) := by
  intro u v p
  simp only [zetaFA]
  split_ifs with h
  · rw [FA_affine P h]; ring
  · ring

/-! ### The global primitive `α₁` (`cons:fer-alpha1`) -/

/-- **`α₁^pre = α₁⁰ − c(p) β − d_C(ζ_𝒜 F_𝒜)`.** -/
def alpha1pre (P : Params) : BForm :=
  alpha10 P - BForm.pmul (corePeriod P) betaB - dCf (zetaFA P)

/-- `A_j(p)`: the `dx_j`-coefficient of `α₁^pre` at `b_j`. -/
def Ajet (P : Params) (j : Fin 3) (p : ℝ) : ℝ := (alpha1pre P).cu (bpoints j).1 (bpoints j).2 p

/-- `B_j(p)`: the `dy_j`-coefficient of `α₁^pre` at `b_j`. -/
def Bjet (P : Params) (j : Fin 3) (p : ℝ) : ℝ := (alpha1pre P).cv (bpoints j).1 (bpoints j).2 p

/-- The cut-off linear function `ζ_j (A_j x_j + B_j y_j)`. -/
def jetFn (P : Params) (j : Fin 3) (u v p : ℝ) : ℝ :=
  zetaJ j u v * (Ajet P j p * centred (bpoints j).1 u + Bjet P j p * centred (bpoints j).2 v)

/-- `Σ_j ζ_j (A_j x_j + B_j y_j)`. -/
def jetSum (P : Params) (u v p : ℝ) : ℝ := ∑ j : Fin 3, jetFn P j u v p

/-- **The global primitive** (eq:fer-alpha1):
`α₁ = α₁⁰ − c(p) β − d_C(ζ_𝒜 F_𝒜) − Σ_j d_C[ζ_j (A_j(p) x_j + B_j(p) y_j)]`. -/
def alpha1 (P : Params) : BForm := alpha1pre P - dCf (jetSum P)

lemma smooth_betaB (c : ℝ → ℝ) (p : ℝ) : (BForm.pmul c betaB).Smooth p :=
  ⟨contDiff_const.mul contDiff_const, contDiff_const.mul (contDiff_bB.comp contDiff_snd)⟩

lemma smooth_alpha1pre (P : Params) (p : ℝ) : (alpha1pre P).Smooth p :=
  ((smooth_alpha10 P p).sub (smooth_betaB _ p)).sub (smooth_dCf (contDiff_zetaFA P p))

lemma contDiff_jetFn (P : Params) (j : Fin 3) (p : ℝ) : ContDiff ℝ ∞ (sl (jetFn P j) p) := by
  have := contDiff_centred_cut (H := fun y => Ajet P j p * y.1 + Bjet P j p * y.2)
    ((contDiff_const.mul contDiff_fst).add (contDiff_const.mul contDiff_snd))
    (bpoints j).1 (bpoints j).2
  exact this

lemma contDiff_jetSum (P : Params) (p : ℝ) : ContDiff ℝ ∞ (sl (jetSum P) p) := by
  have : sl (jetSum P) p = fun x => ∑ j : Fin 3, sl (jetFn P j) p x := rfl
  rw [this]
  exact ContDiff.sum fun j _ => contDiff_jetFn P j p

/-- `α₁` is smooth. -/
theorem smooth_alpha1 (P : Params) (p : ℝ) : (alpha1 P).Smooth p :=
  (smooth_alpha1pre P p).sub (smooth_dCf (contDiff_jetSum P p))

/-- **`d_C α₁ = κ₁ − κ`** (`lem:fer-alpha1`(i)). -/
theorem alpha1_curvature (P : Params) (u v p : ℝ) :
    (alpha1 P).dC u v p = kappa1 P u v p - kappa u v p := by
  have d := fun (α : BForm) (h : α.Smooth p) => (h.smoothOn univ).diffAt isOpen_univ (mem_univ (u, v))
  show (alpha1pre P - dCf (jetSum P)).dC u v p = _
  rw [BForm.dC_sub (d _ (smooth_alpha1pre P p)) (d _ (smooth_dCf (contDiff_jetSum P p))),
    dC_dCf_of_smooth (contDiff_jetSum P p)]
  show (alpha10 P - BForm.pmul (corePeriod P) betaB - dCf (zetaFA P)).dC u v p - 0 = _
  rw [BForm.dC_sub (d _ ((smooth_alpha10 P p).sub (smooth_betaB _ p)))
      (d _ (smooth_dCf (contDiff_zetaFA P p))),
    dC_dCf_of_smooth (contDiff_zetaFA P p),
    BForm.dC_sub (d _ (smooth_alpha10 P p)) (d _ (smooth_betaB _ p)), BForm.dC_pmul,
    supports.2.1.1, d_alpha10]
  ring

lemma pu_const_zero {f : Coef} {u v p : ℝ} (h : sl f p =ᶠ[𝓝 (u, v)] fun _ => 0) :
    pu f u v p = 0 := by
  rw [pu_congr (g := fun _ _ _ => 0) h]; simp [pu]

lemma pv_const_zero {f : Coef} {u v p : ℝ} (h : sl f p =ᶠ[𝓝 (u, v)] fun _ => 0) :
    pv f u v p = 0 := by
  rw [pv_congr (g := fun _ _ _ => 0) h]; simp [pv]

/-! ### `α₁` is affine in `p` and periodic -/

lemma diffAt_u {f : Coef} {p : ℝ} (h : ContDiff ℝ ∞ (sl f p)) (u v : ℝ) :
    DifferentiableAt ℝ (fun s => f s v p) u :=
  differentiableAt_sl_u (h.differentiable (by simp) _)

lemma diffAt_v {f : Coef} {p : ℝ} (h : ContDiff ℝ ∞ (sl f p)) (u v : ℝ) :
    DifferentiableAt ℝ (fun t => f u t p) v :=
  differentiableAt_sl_v (h.differentiable (by simp) _)

lemma alpha1pre_affine (P : Params) : AffineP (alpha1pre P).cu ∧ AffineP (alpha1pre P).cv := by
  obtain ⟨h1, h2⟩ := alpha10_affine P
  have hz := zetaFA_affine P
  constructor
  · intro u v p
    simp only [alpha1pre, BForm.sub_cu, Pi.sub_apply, BForm.pmul, betaB, dCf]
    rw [h1 u v p, hz.pu (diffAt_u (contDiff_zetaFA P 0) u v) (diffAt_u (contDiff_zetaFA P 1) u v)]
    ring
  · intro u v p
    simp only [alpha1pre, BForm.sub_cv, Pi.sub_apply, BForm.pmul, betaB, dCf]
    rw [h2 u v p, hz.pv (diffAt_v (contDiff_zetaFA P 0) u v) (diffAt_v (contDiff_zetaFA P 1) u v),
      corePeriod_affine P p]
    ring

lemma jetSum_affine (P : Params) : AffineP (jetSum P) := by
  intro u v p
  simp only [jetSum, jetFn, Ajet, Bjet, Fin.sum_univ_three]
  rw [(alpha1pre_affine P).1 _ _ p, (alpha1pre_affine P).2 _ _ p,
    (alpha1pre_affine P).1 (bpoints 1).1 _ p, (alpha1pre_affine P).2 (bpoints 1).1 _ p,
    (alpha1pre_affine P).1 (bpoints 2).1 _ p, (alpha1pre_affine P).2 (bpoints 2).1 _ p]
  ring

/-- **`α₁` is affine in `p`** (`lem:fer-alpha1`(i)). -/
theorem alpha1_affine (P : Params) : AffineP (alpha1 P).cu ∧ AffineP (alpha1 P).cv := by
  have hJ := jetSum_affine P
  constructor
  · intro u v p
    simp only [alpha1, BForm.sub_cu, Pi.sub_apply, dCf]
    rw [(alpha1pre_affine P).1 u v p, hJ.pu (diffAt_u (contDiff_jetSum P 0) u v)
      (diffAt_u (contDiff_jetSum P 1) u v)]
    ring
  · intro u v p
    simp only [alpha1, BForm.sub_cv, Pi.sub_apply, dCf]
    rw [(alpha1pre_affine P).2 u v p, hJ.pv (diffAt_v (contDiff_jetSum P 0) u v)
      (diffAt_v (contDiff_jetSum P 1) u v)]
    ring

lemma centred_add_one (c x : ℝ) : centred c (x + 1) = centred c x := by
  rw [centred, centred, show x + 1 - c + 1 / 2 = x - c + 1 / 2 + 1 by ring, Int.fract_add_one]

lemma zetaJ_periodic (j : Fin 3) (u v : ℝ) :
    zetaJ j (u + 1) v = zetaJ j u v ∧ zetaJ j u (v + 1) = zetaJ j u v := by
  simp [zetaJ, centred_add_one]

end SymplecticPacking.Bundle
