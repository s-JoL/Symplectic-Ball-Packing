import SymplecticPacking.General.Ham.SourceSmooth
import SymplecticPacking.General.Ham.FieldIdentity

/-!
# Smoothness of the Hamiltonian of a common isotopy

`sec:ham-hamiltonian`: smoothness of the global Hamiltonian `H = ofIsotopy F r₁ r₂ r₃` on `ℝ × ℝ^{2n}`.

Near a point `(t₀, y₀)` each summand (pushforward along `F_i`) is
* identically `0`, if `y₀` has no preimage in `B̄(r₃)` under `F_i t₀`, or its preimage `u₀` has
  `‖u₀‖ > r₂` (compactness + injectivity: preimages of nearby points are near `u₀`, where the
  source function vanishes); or
* `g_i ∘ Ψ`, if `‖u₀‖ ≤ r₂`, where `Ψ` is the smooth local inverse of `(t,u) ↦ (t, F_i t u)` and
  `g_i = χ · h_i` is smooth (`contDiffOn_sourcePrimitive`).
-/

noncomputable section

namespace SymplecticPacking.General.Ham

open Metric Set Filter ContinuousLinearMap Problem
open scoped ContDiff Topology

variable {n : ℕ}

variable {k : ℕ} {F : Fin k → ℝ → E n → E n} {s : Fin k → E n} {r1 r2 r3 ρ : Fin k → ℝ}

/-- `Φ_i(t,u) = (t, F_i t u)`. -/
def graphMap (F : ℝ → E n → E n) (p : ℝ × E n) : ℝ × E n := (p.1, F p.1 p.2)

/-- **Compactness.** Preimages in `B̄(r₃)` of points near `(t₀, y₀)` are close to the preimages of
`(t₀,y₀)`: for every `δ > 0`, eventually every preimage `u ∈ B̄(r₃)` of `p` lies within `δ` of
some preimage of `(t₀,y₀)` — here, if `(t₀,y₀)` has the preimage `u₀` (resp. none), within `δ` of
`u₀` (resp. there is none). Stated with an arbitrary closed "bad" set `B ⊆ B̄(r₃)` avoided by all
preimages of `(t₀, y₀)`. -/
lemma eventually_no_preimage (hF : CommonIsotopy F s r1 r2 r3 ρ) (i : Fin k) {t₀ : ℝ} {y₀ : E n}
    {B : Set (E n)} (hB : IsClosed B) (hBr : B ⊆ closedBall 0 (r3 i))
    (hno : ∀ u ∈ B, F i t₀ u ≠ y₀) :
    ∀ᶠ p in 𝓝 (t₀, y₀), ∀ u ∈ B, F i p.1 u ≠ p.2 := by
  have hρ := (hF.radii i).2.2.2
  set K : Set (ℝ × E n) := Icc (t₀ - 1) (t₀ + 1) ×ˢ B
  have hKc : IsCompact K :=
    isCompact_Icc.prod ((isCompact_closedBall (0 : E n) (r3 i)).of_isClosed_subset hB hBr)
  have hcont : ContinuousOn (graphMap (F i)) K := by
    apply continuousOn_fst.prodMk
    apply (hF.smooth i).continuousOn.mono
    rintro ⟨t, u⟩ ⟨-, hu⟩
    exact ⟨mem_univ _, mem_ball_zero_iff.mpr
      (lt_of_le_of_lt (mem_closedBall_zero_iff.mp (hBr hu)) hρ)⟩
  have hclosed : IsClosed (graphMap (F i) '' K) := (hKc.image_of_continuousOn hcont).isClosed
  have hnotin : (t₀, y₀) ∉ graphMap (F i) '' K := by
    rintro ⟨⟨t, u⟩, ⟨-, hu⟩, h⟩
    simp only [graphMap, Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    exact hno u hu h
  have h1 : (graphMap (F i) '' K)ᶜ ∈ 𝓝 (t₀, y₀) := hclosed.isOpen_compl.mem_nhds hnotin
  have h2 : Ioo (t₀ - 1) (t₀ + 1) ×ˢ (univ : Set (E n)) ∈ 𝓝 (t₀, y₀) :=
    prod_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)) univ_mem
  filter_upwards [h1, h2] with p hp1 hp2 u hu hpu
  apply hp1
  refine ⟨(p.1, u), ⟨Ioo_subset_Icc_self hp2.1, hu⟩, ?_⟩
  simp [graphMap, hpu]

/-- The derivative of `Φ_i` at `(t₀,u₀)`, an isomorphism since `D_u F` is symplectic. -/
def graphDeriv (F : ℝ → E n → E n) (t₀ : ℝ) (u₀ : E n) : ℝ × E n →L[ℝ] ℝ × E n :=
  (fst ℝ ℝ (E n)).prod (fderiv ℝ (unc F) (t₀, u₀))

lemma graphDeriv_injective {F : ℝ → E n → E n} {t₀ : ℝ} {u₀ : E n}
    (hd : DifferentiableAt ℝ (unc F) (t₀, u₀)) (hA : IsSymplecticLinear (fderiv ℝ (F t₀) u₀)) :
    Function.Injective (graphDeriv F t₀ u₀) := by
  have hinj := IsSymplecticLinear.injective hA
  rw [(hasFDerivAt_slice hd).fderiv] at hinj
  intro p q hpq
  simp only [graphDeriv, prod_apply, coe_fst', Prod.mk.injEq] at hpq
  obtain ⟨h1, h2⟩ := hpq
  have hp : p = (p.1, 0) + (0, p.2) := by simp
  have hq : q = (q.1, 0) + (0, q.2) := by simp
  rw [hp, hq, map_add, map_add, h1] at h2
  have h3 := add_left_cancel h2
  have h4 : p.2 = q.2 := hinj (by simpa using h3)
  exact Prod.ext h1 h4

/-- The equivalence `DΦ_i(t₀,u₀)`. -/
def graphEquiv {F : ℝ → E n → E n} {t₀ : ℝ} {u₀ : E n} (hd : DifferentiableAt ℝ (unc F) (t₀, u₀))
    (hA : IsSymplecticLinear (fderiv ℝ (F t₀) u₀)) : (ℝ × E n) ≃L[ℝ] (ℝ × E n) :=
  (LinearEquiv.ofInjectiveEndo (graphDeriv F t₀ u₀ : (ℝ × E n) →ₗ[ℝ] (ℝ × E n))
    (graphDeriv_injective hd hA)).toContinuousLinearEquiv

lemma graphEquiv_coe {F : ℝ → E n → E n} {t₀ : ℝ} {u₀ : E n}
    (hd : DifferentiableAt ℝ (unc F) (t₀, u₀)) (hA : IsSymplecticLinear (fderiv ℝ (F t₀) u₀)) :
    (graphEquiv hd hA : ℝ × E n →L[ℝ] ℝ × E n) = graphDeriv F t₀ u₀ := by ext v <;> rfl

/-- The source function `g_i = χ · h_i` of the pushforward. -/
def sourceFn (F : ℝ → E n → E n) (r1 r2 : ℝ) (p : ℝ × E n) : ℝ :=
  radialCutoff r1 r2 p.2 * sourcePrimitive F p.1 p.2

/-- Each summand of `H` is smooth at every point. -/
theorem contDiffAt_pushforward (hF : CommonIsotopy F s r1 r2 r3 ρ) (i : Fin k) (p₀ : ℝ × E n) :
    ContDiffAt ℝ ∞ (fun p : ℝ × E n => pushforward (F i) (r3 i)
      (fun t u => radialCutoff (r1 i) (r2 i) u * sourcePrimitive (F i) t u) p.1 p.2) p₀ := by
  obtain ⟨t₀, y₀⟩ := p₀
  obtain ⟨h1r1, hr12, hr23, hr3ρ⟩ := (hF.radii i)
  have hr10 : (0 : ℝ) ≤ (r1 i) := by linarith
  set g := fun t u => radialCutoff (r1 i) (r2 i) u * sourcePrimitive (F i) t u
  -- zero near the point, if all preimages of `(t₀,y₀)` in `B̄(r₃)` lie outside `B̄(r₂)`
  have hzero : (∀ u ∈ closedBall (0 : E n) (r3 i), F i t₀ u = y₀ → (r2 i) < ‖u‖) →
      ContDiffAt ℝ ∞ (fun p : ℝ × E n => pushforward (F i) (r3 i) g p.1 p.2) (t₀, y₀) := by
    intro hfar
    have hev := eventually_no_preimage hF i (B := closedBall (0 : E n) (r2 i)) isClosed_closedBall
      (closedBall_subset_closedBall hr23.le)
      (fun u hu hFu => by
        have := hfar u (closedBall_subset_closedBall hr23.le hu) hFu
        exact absurd (mem_closedBall_zero_iff.mp hu) (not_le.mpr this))
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hev] with p hp
    apply pushforward_eq_zero
    intro u hu hFu
    have hr2u : (r2 i) ≤ ‖u‖ := by
      by_contra h; push Not at h
      exact hp u (mem_closedBall_zero_iff.mpr h.le) hFu
    simp only [g, radialCutoff_eq_zero hr12 hr10 hr2u, zero_mul]
  by_cases hpre : ∃ u₀ ∈ closedBall (0 : E n) (r3 i), F i t₀ u₀ = y₀ ∧ ‖u₀‖ ≤ (r2 i)
  · obtain ⟨u₀, hu₀3, hFu₀, hu₀2⟩ := hpre
    have hu₀ρ : u₀ ∈ ball (0 : E n) (ρ i) := mem_ball_zero_iff.mpr (by linarith)
    have hS := hF.sympFamily i
    have hd := hS.differentiableAt (s := t₀) hu₀ρ
    have hA : IsSymplecticLinear (fderiv ℝ (F i t₀) u₀) := hF.sympl i t₀ u₀ hu₀ρ
    -- the graph map and its local inverse
    have hΦ : ContDiffAt ℝ ∞ (graphMap (F i)) (t₀, u₀) :=
      contDiffAt_fst.prodMk (hS.smooth t₀ u₀ hu₀ρ)
    have hΦ' : HasFDerivAt (graphMap (F i)) ((graphEquiv hd hA : ℝ × E n →L[ℝ] ℝ × E n)) (t₀, u₀) := by
      rw [graphEquiv_coe]
      exact (hasFDerivAt_fst).prodMk hd.hasFDerivAt
    have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
    set Ψ := hΦ.localInverse hΦ' hn
    have hΨs : ContDiffAt ℝ ∞ Ψ (graphMap (F i) (t₀, u₀)) := hΦ.to_localInverse hΦ' hn
    have hstrict := hΦ.hasStrictFDerivAt' hΦ' hn
    have hΨc : ContinuousAt Ψ (graphMap (F i) (t₀, u₀)) := hstrict.localInverse_continuousAt
    have hΨ0 : Ψ (graphMap (F i) (t₀, u₀)) = (t₀, u₀) := hΦ.localInverse_apply_image hΦ' hn
    have hright : ∀ᶠ p in 𝓝 (graphMap (F i) (t₀, u₀)), graphMap (F i) (Ψ p) = p :=
      hstrict.eventually_right_inverse
    have hpt : graphMap (F i) (t₀, u₀) = (t₀, y₀) := by simp [graphMap, hFu₀]
    rw [hpt] at hΨs hΨc hΨ0 hright
    -- `Ψ p` stays in `B(r₃)`
    have hnear : ∀ᶠ p in 𝓝 (t₀, y₀), Ψ p ∈ univ ×ˢ ball u₀ (((r3 i) - (r2 i)) / 2) :=
      hΨc.preimage_mem_nhds (by
        rw [hΨ0]; exact prod_mem_nhds univ_mem (ball_mem_nhds _ (by linarith)))
    -- smoothness of `g` at `(t₀,u₀)`
    have hg : ContDiffAt ℝ ∞ (sourceFn (F i) (r1 i) (r2 i)) (Ψ (t₀, y₀)) := by
      rw [hΨ0]
      have hρ' : (0 : ℝ) ≤ ((r3 i) + (ρ i)) / 2 := by linarith
      have hsm : ContDiffOn ℝ ∞ (fun p : ℝ × E n => sourcePrimitive (F i) p.1 p.2)
          (univ ×ˢ ball (0 : E n) (((r3 i) + (ρ i)) / 2)) :=
        contDiffOn_sourcePrimitive hS (hF.smooth i) hρ' (by linarith)
      have hmem : univ ×ˢ ball (0 : E n) (((r3 i) + (ρ i)) / 2) ∈ 𝓝 (t₀, u₀) :=
        prod_mem_nhds univ_mem (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (by linarith)))
      exact (radialCutoff_contDiff.comp contDiff_snd).contDiffAt.mul (hsm.contDiffAt hmem)
    apply (hg.comp (t₀, y₀) hΨs).congr_of_eventuallyEq
    filter_upwards [hnear, hright] with p hp hpr
    obtain ⟨-, hp2⟩ := hp
    have hΨ1 : (Ψ p).1 = p.1 := by have := congrArg Prod.fst hpr; simpa [graphMap] using this
    have hΨ2 : F i p.1 (Ψ p).2 = p.2 := by
      have := congrArg Prod.snd hpr; simpa [graphMap, hΨ1] using this
    have hΨ3 : (Ψ p).2 ∈ closedBall (0 : E n) (r3 i) := by
      rw [mem_ball, dist_eq_norm] at hp2
      have := norm_le_norm_add_norm_sub' (Ψ p).2 u₀
      exact mem_closedBall_zero_iff.mpr (by linarith)
    show pushforward (F i) (r3 i) g p.1 p.2 = sourceFn (F i) (r1 i) (r2 i) (Ψ p)
    calc pushforward (F i) (r3 i) g p.1 p.2 = pushforward (F i) (r3 i) g p.1 (F i p.1 (Ψ p).2) := by
          rw [hΨ2]
      _ = g p.1 (Ψ p).2 := pushforward_apply_image (hF.inj i p.1) hΨ3
      _ = sourceFn (F i) (r1 i) (r2 i) (Ψ p) := by simp only [g, sourceFn, hΨ1]
  · push Not at hpre
    exact hzero fun u hu hFu => hpre u hu hFu

/-- **`sec:ham-hamiltonian`, smoothness of the global Hamiltonian.** -/
theorem ofIsotopy_smooth (hF : CommonIsotopy F s r1 r2 r3 ρ) :
    ContDiff ℝ ∞ (fun p : ℝ × E n => ofIsotopy F r1 r2 r3 p.1 p.2) := by
  rw [contDiff_iff_contDiffAt]
  intro p₀
  unfold ofIsotopy
  exact ContDiffAt.sum fun i _ => contDiffAt_pushforward hF i p₀

end SymplecticPacking.General.Ham
