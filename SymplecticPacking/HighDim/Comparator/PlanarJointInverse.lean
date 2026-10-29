import SymplecticPacking.HighDim.Comparator.PlanarCritical

/-!
# A local implicit-root theorem for finite-dimensional parameter families
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen

open Set Filter Topology
open scoped ContDiff

/-- A uniquely specified simple zero varies smoothly with all its parameters.
Uniqueness is required only in the open interval containing the zero. -/
theorem contDiffAt_unique_zero {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {G : P → ℝ → ℝ} {root : P → ℝ} {U : Set P} {V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) {y₀ : P} (hy₀ : y₀ ∈ U)
    (hG : ContDiffAt ℝ ∞ (fun p : P × ℝ => G p.1 p.2) (y₀, root y₀))
    (hder : deriv (G y₀) (root y₀) ≠ 0)
    (hroot : ∀ y ∈ U, root y ∈ V ∧ G y (root y) = 0)
    (huniq : ∀ y ∈ U, ∀ t ∈ V, G y t = 0 → t = root y) :
    ContDiffAt ℝ ∞ root y₀ := by
  let x₀ := root y₀
  let Φ : P × ℝ → P × ℝ := fun p => (p.1, G p.1 p.2)
  have hΦ : ContDiffAt ℝ ∞ Φ (y₀, x₀) := contDiffAt_fst.prodMk hG
  let D := fderiv ℝ (fun p : P × ℝ => G p.1 p.2) (y₀, x₀)
  have hGd : HasFDerivAt (fun p : P × ℝ => G p.1 p.2) D (y₀, x₀) :=
    (hG.differentiableAt (by simp)).hasFDerivAt
  have hslice : fderiv ℝ (G y₀) x₀ = D.comp (ContinuousLinearMap.inr ℝ P ℝ) :=
    (hGd.comp x₀ (hasFDerivAt_prodMk_right y₀ x₀)).fderiv
  let Φ' : P × ℝ →L[ℝ] P × ℝ := (ContinuousLinearMap.fst ℝ P ℝ).prod D
  have hΦ'inj : Function.Injective Φ' := by
    intro a b hab
    simp only [Φ', ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    have ha : a = (a.1, 0) + (0, a.2) := by simp
    have hb : b = (b.1, 0) + (0, b.2) := by simp
    rw [ha, hb, map_add, map_add, h1] at h2
    have h3 := add_left_cancel h2
    have h4 : fderiv ℝ (G y₀) x₀ a.2 = fderiv ℝ (G y₀) x₀ b.2 := by
      rw [hslice]
      simpa using h3
    simp only [fderiv_eq_deriv_mul] at h4
    exact Prod.ext h1 (mul_left_cancel₀ hder h4)
  let E : (P × ℝ) ≃L[ℝ] (P × ℝ) :=
    (LinearEquiv.ofInjectiveEndo (Φ' : (P × ℝ) →ₗ[ℝ] (P × ℝ)) hΦ'inj).toContinuousLinearEquiv
  have hE : (E : P × ℝ →L[ℝ] P × ℝ) = Φ' := by ext v <;> rfl
  have hΦ' : HasFDerivAt Φ (E : P × ℝ →L[ℝ] P × ℝ) (y₀, x₀) := by
    rw [hE]
    exact hasFDerivAt_fst.prodMk hGd
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  let Ψ := hΦ.localInverse hΦ' hn
  have hΨs : ContDiffAt ℝ ∞ Ψ (Φ (y₀, x₀)) := hΦ.to_localInverse hΦ' hn
  have hΨpt : Ψ (Φ (y₀, x₀)) = (y₀, x₀) := hΦ.localInverse_apply_image hΦ' hn
  have hright : ∀ᶠ p in 𝓝 (Φ (y₀, x₀)), Φ (Ψ p) = p :=
    (hΦ.hasStrictFDerivAt' hΦ' hn).eventually_right_inverse
  have hpt : Φ (y₀, x₀) = (y₀, 0) := by simp [Φ, x₀, (hroot y₀ hy₀).2]
  rw [hpt] at hΨs hΨpt hright
  have hV' : ∀ᶠ p in 𝓝 (y₀, (0 : ℝ)), (Ψ p).2 ∈ V := by
    apply (continuousAt_snd.comp hΨs.continuousAt).preimage_mem_nhds
    change V ∈ 𝓝 ((Ψ (y₀, 0)).2)
    rw [hΨpt]
    exact hV.mem_nhds (hroot y₀ hy₀).1
  have hinc : Tendsto (fun y : P => (y, (0 : ℝ))) (𝓝 y₀) (𝓝 (y₀, 0)) :=
    (continuous_id.prodMk continuous_const).continuousAt.tendsto
  have hs : ContDiffAt ℝ ∞ (fun y : P => (Ψ (y, 0)).2) y₀ :=
    contDiffAt_snd.comp _ (hΨs.comp y₀ (contDiffAt_id.prodMk contDiffAt_const))
  apply hs.congr_of_eventuallyEq
  filter_upwards [hinc.eventually hright, hinc.eventually hV', hU.mem_nhds hy₀] with y hy hyV hyU
  have hy1 : (Ψ (y, 0)).1 = y := by have hh := congrArg Prod.fst hy; simpa [Φ] using hh
  have hy2 : G y (Ψ (y, 0)).2 = 0 := by have hh := congrArg Prod.snd hy; simpa [Φ, hy1] using hh
  exact (huniq y hyU _ hyV hy2).symm

/-- The unique scalar inverse is jointly smooth for arbitrary finite-dimensional parameters. -/
theorem invR_joint_smooth {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] {G : P → ℝ → ℝ} {U : Set P} (hU : IsOpen U)
    (hG : ∀ y ∈ U, ∀ t, ContDiffAt ℝ ∞ (fun p : P × ℝ => G p.1 p.2) (y, t))
    (hinj : ∀ y ∈ U, Function.Injective (G y))
    (hsurj : ∀ y ∈ U, Function.Surjective (G y))
    (hder : ∀ y ∈ U, ∀ t, deriv (G y) t ≠ 0) :
    ContDiffOn ℝ ∞ (fun p : P × ℝ => Inner.invR (G p.1) p.2) (U ×ˢ univ) := by
  intro p hp
  apply ContDiffAt.contDiffWithinAt
  let root : P × ℝ → ℝ := fun q => Inner.invR (G q.1) q.2
  let F : (P × ℝ) → ℝ → ℝ := fun q t => G q.1 t - q.2
  have hr : ∀ q ∈ U ×ˢ (univ : Set ℝ), G q.1 (root q) = q.2 :=
    fun q hq => Inner.apply_invR (hinj q.1 hq.1) (hsurj q.1 hq.1) q.2
  have hF : ContDiffAt ℝ ∞ (fun x : (P × ℝ) × ℝ => F x.1 x.2) (p, root p) := by
    have h1 := (hG p.1 hp.1 (root p)).comp (p, root p)
      ((contDiffAt_fst.comp _ contDiffAt_fst).prodMk contDiffAt_snd)
    exact h1.sub (contDiffAt_snd.comp _ contDiffAt_fst)
  have hFd : deriv (F p) (root p) ≠ 0 := by
    change deriv (fun t => G p.1 t - p.2) (root p) ≠ 0
    rw [deriv_sub_const]
    exact hder p.1 hp.1 (root p)
  apply contDiffAt_unique_zero (U := U ×ˢ univ) (V := univ) (hU.prod isOpen_univ) isOpen_univ hp hF hFd
    (fun q hq => ⟨mem_univ _, by change G q.1 (root q) - q.2 = 0; rw [hr q hq, sub_self]⟩)
  intro q hq t _ ht
  apply hinj q.1 hq.1
  rw [hr q hq]
  change G q.1 t - q.2 = 0 at ht
  linarith

/-- A smooth right inverse for a finite-dimensional parameter family. -/
theorem param_inverse_smooth {P X : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {G inv : P → X → X} {U : Set P} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ (fun p : P × X => G p.1 p.2) (U ×ˢ univ))
    (hinj : ∀ s ∈ U, Function.Injective (G s))
    (hder : ∀ s ∈ U, ∀ x, Function.Injective (fderiv ℝ (G s) x))
    (hinv : ∀ s ∈ U, ∀ y, G s (inv s y) = y) :
    ContDiffOn ℝ ∞ (fun p : P × X => inv p.1 p.2) (U ×ˢ univ) := by
  rintro ⟨s₀, y₀⟩ ⟨hs₀, -⟩
  apply ContDiffAt.contDiffWithinAt
  set x₀ := inv s₀ y₀
  have hO : U ×ˢ (univ : Set X) ∈ 𝓝 (s₀, x₀) := (hU.prod isOpen_univ).mem_nhds ⟨hs₀, mem_univ _⟩
  have hGa : ContDiffAt ℝ ∞ (fun p : P × X => G p.1 p.2) (s₀, x₀) := hG.contDiffAt hO
  set Φ : P × X → P × X := fun p => (p.1, G p.1 p.2)
  have hΦ : ContDiffAt ℝ ∞ Φ (s₀, x₀) := contDiffAt_fst.prodMk hGa
  set D := fderiv ℝ (fun p : P × X => G p.1 p.2) (s₀, x₀)
  have hGd : HasFDerivAt (fun p : P × X => G p.1 p.2) D (s₀, x₀) :=
    (hGa.differentiableAt (by simp)).hasFDerivAt
  have hslice : fderiv ℝ (G s₀) x₀ = D.comp (ContinuousLinearMap.inr ℝ P X) :=
    (hGd.comp x₀ (hasFDerivAt_prodMk_right s₀ x₀)).fderiv
  set Φ' : P × X →L[ℝ] P × X := (ContinuousLinearMap.fst ℝ P X).prod D
  have hΦ'inj : Function.Injective Φ' := by
    intro a b hab
    simp only [Φ', ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst',
      Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    have ha : a = (a.1, 0) + (0, a.2) := by simp
    have hb : b = (b.1, 0) + (0, b.2) := by simp
    rw [ha, hb, map_add, map_add, h1] at h2
    have h3 := add_left_cancel h2
    have h4 : fderiv ℝ (G s₀) x₀ a.2 = fderiv ℝ (G s₀) x₀ b.2 := by
      rw [hslice]; simpa using h3
    exact Prod.ext h1 (hder s₀ hs₀ x₀ h4)
  set E : (P × X) ≃L[ℝ] (P × X) :=
    (LinearEquiv.ofInjectiveEndo (Φ' : (P × X) →ₗ[ℝ] (P × X)) hΦ'inj).toContinuousLinearEquiv
  have hE : (E : P × X →L[ℝ] P × X) = Φ' := by ext v <;> rfl
  have hΦ' : HasFDerivAt Φ (E : P × X →L[ℝ] P × X) (s₀, x₀) := by
    rw [hE]; exact hasFDerivAt_fst.prodMk hGd
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  set Ψ := hΦ.localInverse hΦ' hn
  have hΨs : ContDiffAt ℝ ∞ Ψ (Φ (s₀, x₀)) := hΦ.to_localInverse hΦ' hn
  have hstrict := hΦ.hasStrictFDerivAt' hΦ' hn
  have hright : ∀ᶠ p in 𝓝 (Φ (s₀, x₀)), Φ (Ψ p) = p := hstrict.eventually_right_inverse
  have hpt : Φ (s₀, x₀) = (s₀, y₀) := by simp only [Φ, x₀, hinv s₀ hs₀]
  rw [hpt] at hΨs hright
  apply (contDiffAt_snd.comp (s₀, y₀) hΨs).congr_of_eventuallyEq
  have hU' : ∀ᶠ p : P × X in 𝓝 (s₀, y₀), p.1 ∈ U :=
    continuous_fst.continuousAt.preimage_mem_nhds (hU.mem_nhds hs₀)
  filter_upwards [hright, hU'] with p hp hpU
  have hΨ1 : (Ψ p).1 = p.1 := by have := congrArg Prod.fst hp; simpa [Φ] using this
  have hΨ2 : G p.1 (Ψ p).2 = p.2 := by have := congrArg Prod.snd hp; simpa [Φ, hΨ1] using this
  apply hinj p.1 hpU
  simp only [Function.comp_apply]
  rw [hinv p.1 hpU, hΨ2]


end SymplecticPacking.HighDim.PlanarGen
