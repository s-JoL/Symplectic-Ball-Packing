import SymplecticPacking.BranchSmall.VectorTransferSpecFlow
import SymplecticPacking.BranchSmall.ReturnPotential
import SymplecticPacking.BranchSmall.HomogeneousGrowth

/-!
# Local control of the reversed Moser return field (supplement prop:vtr-return (c))

`return_control` (in `VectorTransferStages.lean`) asks for `LocalControl` of the reversed Moser
field `s, z ↦ −Y_{1−s}(z)` at a point of the affine chart. This file reduces it to two analytic
statements about the Moser field `returnField a b` of `ω_s = ω_FS + s b dd^c log(1 + |F|²)`:

* `returnField_contDiffOn`: `(s, z) ↦ Y_s(z)` is `C^∞` on an open set containing
  `[0,1] × Affine q` (prop:vtr-return (b),(c): `ω_s` is Kähler for `s ∈ [0,1]`, `b < 1/2`, so the
  linear problem defining `Y_s` is uniquely solvable and its solution depends smoothly on `(s,z)`);
* `returnField_linearGrowth`: `‖Y_s(z)‖ ≤ C (1 + ‖z‖)` for `s ∈ [0,1]` (the field is smooth on
  `CP^{q+1}` and, by its equivariance under the reflection `Z_* ↦ −Z_*` — the equations depend on
  `Z_*` only through `Z_*²` — tangent to the hyperplane at infinity; a smooth field tangent to
  the hyperplane at infinity has at most linear growth in the affine chart).

The reduction is the generic `localControl_of_linearGrowth`, proved here: a field smooth on an
open set containing `[0,1] × E` with linear growth is locally controlled at every point (cut off
in time and space with bump functions; the Grönwall bound keeps the cut-off trajectory inside the
region where the cutoff is one).
-/

noncomputable section

namespace SymplecticPacking.BranchSmall.VT

open Set Filter Topology Metric
open SymplecticPacking.Return (CSField flow flowInv)
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff

/-! ### Cutoffs -/

/-- A function smooth on an open set, multiplied by a smooth function whose topological support
lies in that set, is smooth everywhere. -/
theorem contDiff_smul_of_tsupport_subset {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : X → ℝ} {f : X → F} {U : Set X} (hU : IsOpen U) (hφ : ContDiff ℝ ∞ φ)
    (hf : ContDiffOn ℝ ∞ f U) (hsupp : tsupport φ ⊆ U) :
    ContDiff ℝ ∞ (fun x => φ x • f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ U
  · exact hφ.contDiffAt.smul (hf.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport φ := fun h => hx (hsupp h)
    have hev : (fun x => φ x • f x) =ᶠ[𝓝 x] fun _ => (0 : F) := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx'] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- An open set of `ℝ` containing `[0,1]` contains `[−δ, 1+δ]` for some `δ > 0`. -/
theorem exists_Icc_thicken_subset {u : Set ℝ} (hu : IsOpen u) (hIu : Icc (0 : ℝ) 1 ⊆ u) :
    ∃ δ : ℝ, 0 < δ ∧ Icc (-δ) (1 + δ) ⊆ u := by
  obtain ⟨ε₀, hε₀, h₀⟩ := Metric.isOpen_iff.1 hu 0 (hIu ⟨le_rfl, zero_le_one⟩)
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.isOpen_iff.1 hu 1 (hIu ⟨zero_le_one, le_rfl⟩)
  refine ⟨min ε₀ ε₁ / 2, by positivity, fun x hx => ?_⟩
  have hm0 : min ε₀ ε₁ ≤ ε₀ := min_le_left _ _
  have hm1 : min ε₀ ε₁ ≤ ε₁ := min_le_right _ _
  have hmp : 0 < min ε₀ ε₁ := lt_min hε₀ hε₁
  rcases lt_or_ge x 0 with h | h
  · apply h₀
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_neg h]
    linarith [hx.1]
  · rcases le_or_gt x 1 with h' | h'
    · exact hIu ⟨h, h'⟩
    · apply h₁
      rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
      linarith [hx.2]

section generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

/-- **Generic local control.** A time-dependent field that is `C^∞` on an open set containing
`[0,1] × E` and has linear growth for `s ∈ [0,1]` is locally controlled at every point. -/
theorem localControl_of_linearGrowth {V : ℝ → E → E} {U : Set (ℝ × E)} (hU : IsOpen U)
    (hIU : Icc (0 : ℝ) 1 ×ˢ (univ : Set E) ⊆ U)
    (hV : ContDiffOn ℝ ∞ (fun p : ℝ × E => V p.1 p.2) U)
    {C : ℝ} (hC : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z, ‖V s z‖ ≤ C * (1 + ‖z‖)) (y : E) :
    LocalControl V y := by
  set C' := max C 1 with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set R : ℝ := (‖y‖ + 1) * Real.exp C' + 1 with hR
  have hR0 : 0 < R := by positivity
  -- a product neighbourhood of `[0,1] × closedBall 0 (R+1)` inside `U`
  obtain ⟨u, v, hu, hv, hIu, hBv, huv⟩ := generalized_tube_lemma isCompact_Icc
    (isCompact_closedBall (0 : E) (R + 1)) hU (fun p hp => hIU ⟨hp.1, mem_univ _⟩)
  obtain ⟨δ, hδ, hδu⟩ := exists_Icc_thicken_subset hu hIu
  -- the bumps
  let ρ : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2, 1 / 2 + δ, by norm_num, by linarith⟩
  let χ : ContDiffBump (0 : E) := ⟨R, R + 1, hR0, by linarith⟩
  let φ : ℝ × E → ℝ := fun p => ρ p.1 * χ p.2
  have hφ : ContDiff ℝ ∞ φ :=
    (ρ.contDiff.comp contDiff_fst).mul (χ.contDiff.comp contDiff_snd)
  have hρI : closedBall (1 / 2 : ℝ) (1 / 2 + δ) ⊆ u := by
    intro s hs
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hs
    exact hδu ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hsuppK : tsupport φ ⊆ closedBall (1 / 2 : ℝ) (1 / 2 + δ) ×ˢ closedBall (0 : E) (R + 1) := by
    apply closure_minimal _ (isClosed_closedBall.prod isClosed_closedBall)
    intro p hp
    have hp' : ρ p.1 * χ p.2 ≠ 0 := hp
    have h1 : p.1 ∈ tsupport ρ := subset_tsupport _ (left_ne_zero_of_mul hp')
    have h2 : p.2 ∈ tsupport χ := subset_tsupport _ (right_ne_zero_of_mul hp')
    rw [ρ.tsupport_eq] at h1
    rw [χ.tsupport_eq] at h2
    exact ⟨h1, h2⟩
  have hsupp : tsupport φ ⊆ U := fun p hp => by
    have := hsuppK hp
    exact huv ⟨hρI this.1, hBv this.2⟩
  have hφc : HasCompactSupport φ :=
    ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _)).of_isClosed_subset
      (isClosed_tsupport φ) hsuppK
  -- the cut-off field
  let W : ℝ → E → E := fun s z => φ (s, z) • V s z
  have hW : CSField W := by
    refine ⟨?_, ?_⟩
    · exact contDiff_smul_of_tsupport_subset hU hφ hV hsupp
    · change HasCompactSupport (φ • fun p : ℝ × E => V p.1 p.2)
      exact hφc.smul_right
  have hφ1 : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z ∈ ball (0 : E) R, φ (s, z) = 1 := by
    intro s hs z hz
    have h1 : ρ s = 1 := by
      apply ρ.one_of_mem_closedBall
      change s ∈ closedBall (1 / 2 : ℝ) (1 / 2)
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
      exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have h2 : χ z = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hz)
    change ρ s * χ z = 1
    rw [h1, h2, one_mul]
  have hagree : AgreesOn V W (ball (0 : E) R) := by
    intro s hs z hz
    change V s z = φ (s, z) • V s z
    rw [hφ1 s hs z hz, one_smul]
  refine ⟨W, ball (0 : E) R, hW, isOpen_ball, hagree, ?_⟩
  -- Grönwall
  have hWb : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z, ‖W s z‖ ≤ C' * ‖z‖ + C' := by
    intro s hs z
    have h0 : 0 ≤ φ (s, z) := mul_nonneg (ρ.nonneg) (χ.nonneg)
    have h1 : φ (s, z) ≤ 1 := by
      change ρ s * χ z ≤ 1
      calc ρ s * χ z ≤ 1 * 1 :=
            mul_le_mul ρ.le_one χ.le_one χ.nonneg zero_le_one
        _ = 1 := one_mul 1
    change ‖φ (s, z) • V s z‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg h0]
    have hVb := hC s hs z
    have hCC : C * (1 + ‖z‖) ≤ C' * (1 + ‖z‖) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hn : 0 ≤ ‖V s z‖ := norm_nonneg _
    nlinarith
  intro s hs
  have hcont : ContinuousOn (fun t => flow W t y) (Icc 0 1) :=
    fun t _ => (hW.flow_hasDerivAt y t).continuousAt.continuousWithinAt
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le (f := fun t => flow W t y)
    (f' := fun t => W t (flow W t y)) (δ := ‖y‖) (K := C') (ε := C') hcont
    (fun t _ => (hW.flow_hasDerivAt y t).hasDerivWithinAt)
    (by simp only [hW.flow_zero, le_refl])
    (fun t ht => hWb t ⟨ht.1, ht.2.le⟩ _) s hs
  rw [gronwallBound_of_K_ne_0 hC'pos.ne', div_self hC'pos.ne'] at hg
  simp only [one_mul, sub_zero] at hg
  have he : Real.exp (C' * s) ≤ Real.exp C' :=
    Real.exp_le_exp.2 (by nlinarith [hs.1, hs.2])
  have hy := norm_nonneg y
  rw [Metric.mem_ball, dist_zero_right]
  have hepos := Real.exp_pos (C' * s)
  nlinarith

/-- Local control of the reversed field from the hypotheses of `localControl_of_linearGrowth`
for the forward field. -/
theorem localControl_revField_of_linearGrowth {V : ℝ → E → E} {U : Set (ℝ × E)} (hU : IsOpen U)
    (hIU : Icc (0 : ℝ) 1 ×ˢ (univ : Set E) ⊆ U)
    (hV : ContDiffOn ℝ ∞ (fun p : ℝ × E => V p.1 p.2) U)
    {C : ℝ} (hC : ∀ s ∈ Icc (0 : ℝ) 1, ∀ z, ‖V s z‖ ≤ C * (1 + ‖z‖)) (y : E) :
    LocalControl (revField V) y := by
  let r : ℝ × E → ℝ × E := fun p => (1 - p.1, p.2)
  have hr : ContDiff ℝ ∞ r := (contDiff_const.sub contDiff_fst).prodMk contDiff_snd
  refine localControl_of_linearGrowth (U := r ⁻¹' U) (hU.preimage hr.continuous) ?_ ?_ (C := C)
    ?_ y
  · rintro ⟨s, z⟩ ⟨hs, -⟩
    exact hIU ⟨⟨by linarith [hs.2], by linarith [hs.1]⟩, mem_univ _⟩
  · have h := (hV.comp hr.contDiffOn (fun p hp => hp)).neg
    exact h
  · intro s hs z
    simp only [revField, norm_neg]
    exact hC (1 - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩ z

end generic

/-! ### The analytic inputs for the Moser return field -/

/-! ### Smooth dependence of the solution of a nondegenerate linear problem -/

section solve

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

omit [CompleteSpace E] in
theorem finrank_eq_finrank_clm_dual : Module.finrank ℝ E = Module.finrank ℝ (E →L[ℝ] ℝ) :=
  (Subspace.dual_finrank_eq (K := ℝ) (V := E)).symm.trans
    (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).finrank_eq

omit [CompleteSpace E] in
/-- An injective `B : E →L (E →L ℝ)` is a continuous linear equivalence. -/
theorem exists_equiv_of_injective {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : Function.Injective B) :
    ∃ e : E ≃L[ℝ] (E →L[ℝ] ℝ), (e : E →L[ℝ] E →L[ℝ] ℝ) = B :=
  ⟨(LinearEquiv.ofInjectiveOfFinrankEq (B : E →ₗ[ℝ] E →L[ℝ] ℝ) hB
    finrank_eq_finrank_clm_dual).toContinuousLinearEquiv, by ext; rfl⟩

/-- **Smoothness of the solution of a smooth nondegenerate linear problem.** If `B`, `c` are
`C^∞` and `G x` solves `B x (G x) = c x` whenever the solution is unique, then `G` is `C^∞` on an
open set containing every `x` at which `B x` is injective. -/
theorem contDiffOn_of_unique_solution {B : X → E →L[ℝ] E →L[ℝ] ℝ} {c : X → E →L[ℝ] ℝ}
    (hB : ContDiff ℝ ∞ B) (hc : ContDiff ℝ ∞ c) {G : X → E}
    (hG : ∀ x, (∃! Y : E, B x Y = c x) → B x (G x) = c x) :
    ∃ U : Set X, IsOpen U ∧ {x | Function.Injective (B x)} ⊆ U ∧ ContDiffOn ℝ ∞ G U := by
  let U : Set X := B ⁻¹' range ((↑) : (E ≃L[ℝ] (E →L[ℝ] ℝ)) → E →L[ℝ] E →L[ℝ] ℝ)
  have hU : IsOpen U := ContinuousLinearEquiv.isOpen.preimage hB.continuous
  refine ⟨U, hU, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨e, he⟩ := exists_equiv_of_injective hx
    exact ⟨e, he⟩
  · -- near `x`, `G = inverse (B ·) (c ·)`
    have hev : G =ᶠ[𝓝 x] fun y => ContinuousLinearMap.inverse (B y) (c y) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      obtain ⟨e, he⟩ := hy
      have huniq : ∃! Y : E, B y Y = c y := by
        refine ⟨e.symm (c y), ?_, fun Y hY => ?_⟩
        · rw [← he]
          exact e.apply_symm_apply (c y)
        · apply e.injective
          rw [e.apply_symm_apply]
          have : (e : E →L[ℝ] E →L[ℝ] ℝ) Y = c y := by rw [he]; exact hY
          exact this
      have hGy := hG y huniq
      rw [← he, ContinuousLinearMap.inverse_equiv]
      apply e.injective
      rw [ContinuousLinearEquiv.coe_coe, e.apply_symm_apply]
      have : (e : E →L[ℝ] E →L[ℝ] ℝ) (G y) = c y := by rw [he]; exact hGy
      exact this
    obtain ⟨e, he⟩ := hx
    have hinv : ContDiffAt ℝ ∞ (fun y => ContinuousLinearMap.inverse (B y)) x := by
      have h1 := contDiffAt_map_inverse (n := ∞) e
      rw [he] at h1
      exact h1.comp x hB.contDiffAt
    exact ((hinv.clm_apply hc.contDiffAt).congr_of_eventuallyEq hev).contDiffWithinAt

end solve

/-! ### The analytic inputs for the Moser return field -/

/-! #### Smoothness of `d^c`, `dd^c` of smooth potentials -/

section ddc

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F]
  [IsScalarTower ℝ ℂ F]

theorem dcForm_contDiff_of {Φ : F → ℝ} (hΦ : ContDiff ℝ ∞ Φ) : ContDiff ℝ ∞ (dcForm Φ) := by
  unfold dcForm
  exact (((contDiff_infty_iff_fderiv.1 hΦ).2).clm_comp contDiff_const).const_smul _

/-- Joint smoothness of `d^c` of a smooth family of potentials. -/
theorem dcForm_family_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {Φ : X → F → ℝ} (hΦ : ContDiff ℝ ∞ (fun p : X × F => Φ p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : X × F => dcForm (Φ p.1) p.2) := by
  have hf : ContDiff ℝ ∞ (Function.uncurry fun (p : X × F) (z : F) => Φ p.1 z) :=
    hΦ.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd := ContDiff.fderiv (𝕜 := ℝ) hf contDiff_snd (n := ∞) (by simp)
  unfold dcForm
  exact (hd.clm_comp contDiff_const).const_smul _

/-- Joint smoothness of `dd^c` of a smooth family of potentials. -/
theorem ddcForm_family_contDiff [FiniteDimensional ℝ F] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X]
    {Φ : X → F → ℝ} (hΦ : ContDiff ℝ ∞ (fun p : X × F => Φ p.1 p.2)) :
    ContDiff ℝ ∞ (fun p : X × F => ddcForm (Φ p.1) p.2) := by
  have hα := dcForm_family_contDiff hΦ
  have hf : ContDiff ℝ ∞ (Function.uncurry fun (p : X × F) (z : F) => dcForm (Φ p.1) z) :=
    hα.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hd : ContDiff ℝ ∞ (fun p : X × F => fderiv ℝ (dcForm (Φ p.1)) p.2) :=
    ContDiff.fderiv (𝕜 := ℝ) hf contDiff_snd (n := ∞) (by simp)
  have hfl : ContDiff ℝ ∞ (fun p : X × F => (fderiv ℝ (dcForm (Φ p.1)) p.2).flip) := by
    rw [contDiff_clm_apply_iff]
    intro v
    rw [contDiff_clm_apply_iff]
    intro w
    exact (hd.clm_apply contDiff_const).clm_apply contDiff_const
  unfold ddcForm euclideanExteriorOneForm
  exact hd.sub hfl

end ddc

private theorem rc_wsq_contDiff {q : ℕ} : ContDiff ℝ ∞ (wsq (q := q)) := by
  unfold wsq
  apply ContDiff.sum
  intro j _
  have : (fun w : Fin q → ℂ => Complex.normSq (w j)) =
      fun w => (w j).re * (w j).re + (w j).im * (w j).im := by
    funext w; exact Complex.normSq_apply _
  rw [this]
  have hre : ContDiff ℝ ∞ (fun w : Fin q → ℂ => (w j).re) :=
    Complex.reCLM.contDiff.comp (contDiff_apply ℝ ℂ j)
  have him : ContDiff ℝ ∞ (fun w : Fin q → ℂ => (w j).im) :=
    Complex.imCLM.contDiff.comp (contDiff_apply ℝ ℂ j)
  exact (hre.mul hre).add (him.mul him)

private theorem rc_nsq_contDiff {q : ℕ} : ContDiff ℝ ∞ (nsq (q := q)) := by
  unfold nsq
  have h1 : ContDiff ℝ ∞ (fun z : Affine q => Complex.normSq z.1) := by
    have : (fun z : Affine q => Complex.normSq z.1) =
        fun z => z.1.re * z.1.re + z.1.im * z.1.im := by
      funext z; exact Complex.normSq_apply _
    rw [this]
    have hre : ContDiff ℝ ∞ (fun z : Affine q => z.1.re) := Complex.reCLM.contDiff.comp contDiff_fst
    have him : ContDiff ℝ ∞ (fun z : Affine q => z.1.im) := Complex.imCLM.contDiff.comp contDiff_fst
    exact (hre.mul hre).add (him.mul him)
  exact h1.add (rc_wsq_contDiff.comp contDiff_snd)

theorem fsPot_contDiff {q : ℕ} : ContDiff ℝ ∞ (fun z : Affine q => Real.log (1 + nsq z)) :=
  (contDiff_const.add rc_nsq_contDiff).log fun z => (one_add_nsq_pos z).ne'

theorem graphPot_contDiff {q : ℕ} (a : Fin q → ℂ) : ContDiff ℝ ∞ (graphPot a) := by
  unfold graphPot
  have he : ContDiff ℝ ∞ (equations a) := (equations_contDiff a).restrict_scalars ℝ
  have hq : ContDiff ℝ ∞ (fun z : Affine q => wsq (equations a z) / (1 + nsq z) ^ 2) :=
    (rc_wsq_contDiff.comp he).div ((contDiff_const.add rc_nsq_contDiff).pow 2)
      fun z => (pow_pos (one_add_nsq_pos z) 2).ne'
  refine (contDiff_const.add hq).log fun z => ?_
  have h1 := wsq_nonneg (equations a z)
  have h2 := pow_pos (one_add_nsq_pos z) 2
  have : 0 ≤ wsq (equations a z) / (1 + nsq z) ^ 2 := div_nonneg h1 h2.le
  linarith

/-- **Smoothness of the Moser forms** (lem:vtr-form): `(s, z) ↦ ω_s(z)` is `C^∞`. The potential
`log(1 + |z|²) + s b log(1 + |F|²)` is `C^∞` and affine in `s`, so `ω_s = dd^c(...)` is the
`C^∞` family `ω_0 + s b dd^c log(1 + |F|²)`. -/
theorem returnForm_contDiff (m : ℕ) (b : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Affine (m + 2) => ddcForm (returnPot (parameters m) b p.1) p.2) := by
  apply ddcForm_family_contDiff (Φ := returnPot (parameters m) b)
  unfold returnPot
  exact (fsPot_contDiff.comp contDiff_snd).add
    ((contDiff_fst.mul contDiff_const).mul ((graphPot_contDiff _).comp contDiff_snd))

/-- The covector `−b d^c log(1 + |F|²)` is `C^∞`. -/
theorem returnCovector_contDiff (m : ℕ) (b : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × Affine (m + 2) => (-b) • dcForm (graphPot (parameters m)) p.2) :=
  ((dcForm_contDiff_of (graphPot_contDiff _)).comp contDiff_snd).const_smul (-b)

/-- **`ω_s` is Kähler** (prop:vtr-return (b)): for `0 < b < 1/2` and `s ∈ [0,1]`,
`ω_s(v, i v) > 0` for `v ≠ 0`. Here
`ω_s = (1 − 2sb) ω_FS + s b dd^c log((1 + |z|²)² + |F(z)|²)`: the first term is positive
(`1 − 2sb ≥ 1 − 2b > 0`), the second is `dd^c` of the logarithm of a sum of squared moduli of
holomorphic functions without common zero, hence nonnegative on `(v, i v)`. (Convention check:
for the potential `|z|²` on `ℂ`, `dd^c|z|²(v, w) = Im(v̄ w)/π`, so `(v, i v) ↦ |v|²/π`.) -/
theorem returnForm_pos (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (z v : Affine (m + 2)) (hv : v ≠ 0) :
    0 < ddcForm (returnPot (parameters m) b s) z v (Complex.I • v) := by
  rw [returnPot_ddc]
  exact normalAmbientForm_positive _ (one_div_pos.mpr Real.pi_pos)
    (mul_nonneg hs.1 hb0.le) (by nlinarith [hs.2]) 1 z v hv

/-- **`ω_s` is nondegenerate**: `Y ↦ ω_s(Y, ·)` is injective for `s ∈ [0,1]`. -/
theorem returnForm_injective (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (z : Affine (m + 2)) :
    Function.Injective (ddcForm (returnPot (parameters m) b s) z) := by
  intro Y₁ Y₂ h
  by_contra hne
  have hv : Y₁ - Y₂ ≠ 0 := sub_ne_zero.2 hne
  have h0 : ddcForm (returnPot (parameters m) b s) z (Y₁ - Y₂) = 0 := by
    rw [map_sub, h, sub_self]
  have hp := returnForm_pos m hb0 hb hs z (Y₁ - Y₂) hv
  rw [h0, ContinuousLinearMap.zero_apply] at hp
  exact lt_irrefl _ hp

/-- **Smoothness of the Moser field** (prop:vtr-return (b),(c)): for `0 < b < 1/2`,
`(s, z) ↦ Y_s(z)` is `C^∞` on an open set containing `[0,1] × Affine (m+2)`. -/
theorem returnField_contDiffOn (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    ∃ U : Set (ℝ × Affine (m + 2)), IsOpen U ∧ Icc (0 : ℝ) 1 ×ˢ (univ : Set (Affine (m + 2))) ⊆ U ∧
      ContDiffOn ℝ ∞ (fun p : ℝ × Affine (m + 2) => returnField (parameters m) b p.1 p.2) U := by
  obtain ⟨U, hU, hNU, hG⟩ := contDiffOn_of_unique_solution (returnForm_contDiff m b)
    (returnCovector_contDiff m b)
    (G := fun p : ℝ × Affine (m + 2) => returnField (parameters m) b p.1 p.2) (by
      rintro ⟨s, z⟩ h
      have h' : ∃! Y : Affine (m + 2), ∀ v, ddcForm (returnPot (parameters m) b s) z Y v =
          -b * dcForm (graphPot (parameters m)) z v := by
        obtain ⟨Y, hY, hYu⟩ := h
        refine ⟨Y, fun v => ?_, fun Y' hY' => hYu Y' ?_⟩
        · have := congrArg (fun f => f v) hY
          simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using this
        · refine ContinuousLinearMap.ext fun v => ?_
          simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using hY' v
      have hsp := SymplecticPacking.Explicit.the_spec h'
      change ddcForm (returnPot (parameters m) b s) z (returnField (parameters m) b s z) =
        (-b) • dcForm (graphPot (parameters m)) z
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [returnField, dif_pos h', ContinuousLinearMap.smul_apply, smul_eq_mul]
      exact hsp v)
  refine ⟨U, hU, fun p hp => hNU ?_, hG⟩
  exact returnForm_injective m hb0 hb hp.1 p.2

/-- **Linear growth of the Moser field** (prop:vtr-return (c),(d) with the reflection
`Z_* ↦ −Z_*`): the field extends smoothly to `CP^{m+3}` and is tangent to the hyperplane at
infinity (fixed by the reflection, which preserves all the data), so in the affine chart
`‖Y_s(z)‖ ≤ C (1 + ‖z‖)` for `s ∈ [0,1]`. -/
theorem returnField_linearGrowth (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    ∃ C : ℝ, ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : Affine (m + 2),
      ‖returnField (parameters m) b s z‖ ≤ C * (1 + ‖z‖) := by
  exact returnField_linearGrowth_homogeneous (parameters m) hb0.le hb

/-- **Return, local control** at every point of the affine chart. -/
theorem return_control_all (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) (z : Affine (m + 2)) :
    LocalControl (revField (returnField (parameters m) b)) z := by
  obtain ⟨U, hU, hIU, hV⟩ := returnField_contDiffOn m hb0 hb
  obtain ⟨C, hC⟩ := returnField_linearGrowth m hb0 hb
  exact localControl_revField_of_linearGrowth hU hIU hV hC z

end SymplecticPacking.BranchSmall.VT
