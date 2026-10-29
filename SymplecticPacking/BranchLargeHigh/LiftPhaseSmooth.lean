import SymplecticPacking.BranchLargeHigh.ChartLift
import OAI.Geometry.BallPacking.DiskMaps.FlatIsotopy
import OAI.Geometry.BallPacking.Annuli.AnnularMean

/-!
# Smoothness of the lift phase `Ψ = zeroPhase + radialPhase` (supplement `lem:two-identification`)

The zero section is fixed, so `zeroPhase = 0` (`ChartLift.lean`). The phase is therefore
its radial line-action integral. The segment stays in the transfer tube; localized
parameter integration proves smoothness on the tube.
-/

noncomputable section

namespace SymplecticPacking.BranchLargeHigh.Two.LiftSmooth

open Set Filter Topology MeasureTheory Manifold
open SymplecticPacking.HighDim
open SymplecticPacking.Return (CSField flow)
open OAI.PackingSufficiencySupport (Ambient)
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold

/-! ### Generic calculus -/

theorem lamAmb_contDiff {n : ℕ} :
    ContDiff ℝ ∞ (fun p : Ambient n × Ambient n => lamAmb p.1 p.2) := by
  unfold lamAmb
  apply ContDiff.div_const
  apply ContDiff.sum
  intro i _
  have h1 : ContDiff ℝ ∞ (fun p : Ambient n × Ambient n => p.1 i) :=
    (contDiff_apply ℝ ℂ i).comp contDiff_fst
  have h2 : ContDiff ℝ ∞ (fun p : Ambient n × Ambient n => p.2 i) :=
    (contDiff_apply ℝ ℂ i).comp contDiff_snd
  exact Complex.imCLM.contDiff.comp ((Complex.conjCLE.contDiff.comp h1).mul h2)

/-- **Localized parametric integral.** If `f` is smooth on an open set containing
`[0,1] × {p₀}`, then `p ↦ ∫₀¹ f(t,p) dt` is smooth at `p₀`. -/
theorem integral_contDiffAt_of_open {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {W : Set (ℝ × P)} (hW : IsOpen W) {f : ℝ × P → F} (hf : ContDiffOn ℝ ∞ f W) {p₀ : P}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, (t, p₀) ∈ W) :
    ContDiffAt ℝ ∞ (fun p => ∫ t in (0 : ℝ)..1, f (t, p)) p₀ := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ ({p₀} : Set P)) := isCompact_Icc.prod isCompact_singleton
  obtain ⟨δ, hδ, hth⟩ := hK.exists_thickening_subset_open hW (by
    rintro ⟨t, p⟩ ⟨ht, hp⟩
    rw [mem_singleton_iff] at hp
    subst hp
    exact h t ht)
  have hsub : ∀ t p, t ∈ Ioo (-δ) (1 + δ) → dist p p₀ < δ → ((t, p) : ℝ × P) ∈ W := by
    intro t p ht hp
    apply hth
    rw [Metric.mem_thickening_iff]
    refine ⟨(max 0 (min 1 t), p₀),
      ⟨⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩, rfl⟩, ?_⟩
    rw [Prod.dist_eq]
    refine max_lt ?_ hp
    rw [Real.dist_eq, abs_lt]
    obtain ⟨ht1, ht2⟩ := ht
    constructor <;> (simp only [max_def, min_def]; split_ifs <;> linarith)
  let c : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2, 1 / 2 + δ / 2, by norm_num, by linarith⟩
  have hcO : c.rOut = 1 / 2 + δ / 2 := rfl
  have hcI : c.rIn = 1 / 2 := rfl
  have hg : ContDiffOn ℝ ∞ (fun q : ℝ × P => c q.1 • f q) (univ ×ˢ Metric.ball p₀ δ) := by
    intro q hq
    have hqU : dist q.2 p₀ < δ := hq.2
    by_cases hq1 : dist q.1 (1 / 2) < 1 / 2 + δ
    · have hqW : q ∈ W := by
        apply hsub q.1 q.2 _ hqU
        rw [Real.dist_eq, abs_lt] at hq1
        exact ⟨by linarith [hq1.1], by linarith [hq1.2]⟩
      exact (((c.contDiff (n := ⊤)).comp contDiff_fst).contDiffAt.smul
        (hf.contDiffAt (hW.mem_nhds hqW))).contDiffWithinAt
    · have hnot : q.1 ∉ tsupport c := by
        rw [c.tsupport_eq, hcO]
        intro hm
        have : dist q.1 (1 / 2) ≤ 1 / 2 + δ / 2 := hm
        exact hq1 (by linarith)
      have h1 := notMem_tsupport_iff_eventuallyEq.mp hnot
      have h2 := (continuous_fst.tendsto q).eventually h1
      apply ContDiffAt.contDiffWithinAt
      apply (contDiffAt_const (c := (0 : F))).congr_of_eventuallyEq
      filter_upwards [h2] with q' hq'
      simp only [Pi.zero_apply] at hq'
      simp [hq']
  have hI := OAI.PackingSufficiencySupport.Hamiltonian.contDiffOn_fixed_integral
    Metric.isOpen_ball hg
  have hI' := hI.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))
  apply hI'.congr_of_eventuallyEq
  filter_upwards with p
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have hc1 : c t = 1 := c.one_of_mem_closedBall (by
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le, hcI]
    constructor <;> linarith [ht.1, ht.2])
  simp [hc1]

/-! ### Local smoothness of the stages -/

theorem wsq_toC_smul {n : ℕ} (t : ℝ) (w : Fibre n) :
    BranchSmall.VT.wsq (BranchSmall.VT.toC (t • w)) = t ^ 2 * BranchSmall.VT.wsq (BranchSmall.VT.toC w) := by
  simp only [BranchSmall.VT.wsq, BranchSmall.VT.toC, Complex.normSq_mk, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem returnInv_contDiff (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    ContDiff ℝ ∞ (BranchSmall.VT.returnInv (parameters m) b) :=
  contDiff_iff_contDiffAt.2 fun z =>
    BranchSmall.VT.flowI_back_contDiffAt_of_control (BranchSmall.VT.return_control_all m hb0 hb z)

theorem transport_eventually_contDiffAt (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (x : Affine (m + 2) × Fibre (m + 2)) (hx : x ∈ BranchSmall.VT.tube (parameters m) b) :
    ∀ᶠ y in 𝓝 (BranchSmall.VT.stageR b x),
      ContDiffAt ℝ ∞ (BranchSmall.VT.transport (parameters m) b) y := by
  obtain ⟨W, O, hW, hO, hVW, hy⟩ := BranchSmall.VT.transport_control m hb0 hb x hx
  filter_upwards [BranchSmall.VT.staysIn_eventually hW hO hy] with y hy'
  exact BranchSmall.VT.flowI_one_contDiffAt hW hO hVW hy'

theorem transferMap_eventually_contDiffAt (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (x : Affine (m + 2) × Fibre (m + 2)) (hx : x ∈ BranchSmall.VT.tube (parameters m) b) :
    ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ (BranchSmall.VT.transferMap (parameters m) b) y := by
  have hc : Continuous (fun y : Affine (m + 2) × Fibre (m + 2) =>
      Real.pi * BranchSmall.VT.wsq (BranchSmall.VT.toC y.2)) :=
    continuous_const.mul (BranchSmall.VT.wsq_continuous.comp
      (BranchSmall.VT.toC_continuous.comp continuous_snd))
  have hR : ∀ᶠ y in 𝓝 x, Real.pi * BranchSmall.VT.wsq (BranchSmall.VT.toC y.2) < b :=
    (hc.tendsto x).eventually (eventually_lt_nhds hx.2)
  have hT := ((BranchSmall.VT.stageR_contDiffAt (b := b) x hx.2).continuousAt.tendsto).eventually
    (transport_eventually_contDiffAt m hb0 hb x hx)
  filter_upwards [hR, hT] with y hy hyT
  rw [BranchSmall.VT.transferMap_eq_comp]
  exact (affineRadialTarget_smooth (m + 2) (1 / Real.pi)).contDiffAt.comp y
    ((returnInv_contDiff m hb0 hb).contDiffAt.comp y
      (contDiffAt_fst.comp y (hyT.comp y (BranchSmall.VT.stageR_contDiffAt y hy))))

/-! ### The radial phase on the affine chart -/

variable (q : ℕ) (h₂ : ℝ)

/-- The radial action as a function on `Affine × Fibre`. -/
def radialAct (p : Affine (q + 2) × Fibre (q + 2)) : ℝ :=
  lineAction (fun t => BranchSmall.VT.transferMap (parameters q) (transferHeight h₂) (p.1, t • p.2))

variable {q h₂}

theorem transferHeight_pos (hh : 0 < h₂) : 0 < transferHeight h₂ := by
  unfold transferHeight; linarith

theorem transferHeight_lt (hh2 : h₂ < 1 / 2) : transferHeight h₂ < 1 / 2 := by
  unfold transferHeight; linarith

/-- **Segment line action** (generic): if `φ` is smooth at every point of an open set `U`
containing the segment `t ↦ (p₀.1, t p₀.2)`, `t ∈ [0,1]`, the line action of the segment is
smooth at `p₀`. -/
theorem segment_lineAction_contDiffAt {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [FiniteDimensional ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
    {n : ℕ} {φ : A × B → Ambient n} {U : Set (A × B)} (hUo : IsOpen U)
    (hφU : ∀ y ∈ U, ContDiffAt ℝ ∞ φ y) {p₀ : A × B}
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, ((p₀.1, t • p₀.2) : A × B) ∈ U) :
    ContDiffAt ℝ ∞ (fun p : A × B => lineAction (fun t => φ (p.1, t • p.2))) p₀ := by
  have hφ : ContDiffOn ℝ ∞ φ U := fun y hy => (hφU y hy).contDiffWithinAt
  let σ : ℝ × (A × B) → A × B := fun tp => (tp.2.1, tp.1 • tp.2.2)
  have hσ : ContDiff ℝ ∞ σ :=
    (contDiff_snd.fst).prodMk (contDiff_fst.smul contDiff_snd.snd)
  have hWo : IsOpen (σ ⁻¹' U) := hUo.preimage hσ.continuous
  have h1 : ContDiffOn ℝ ∞ (fun tp => φ (σ tp)) (σ ⁻¹' U) :=
    hφ.comp hσ.contDiffOn (fun _ h => h)
  have hD : ContDiffOn ℝ ∞ (fun y => fderiv ℝ φ y) U := hφ.fderiv_of_isOpen hUo (by simp)
  have h2 : ContDiffOn ℝ ∞ (fun tp : ℝ × (A × B) => fderiv ℝ φ (σ tp) ((0 : A), tp.2.2))
      (σ ⁻¹' U) :=
    (hD.comp hσ.contDiffOn (fun _ h => h)).clm_apply
      (contDiff_const.prodMk contDiff_snd.snd).contDiffOn
  have hF : ContDiffOn ℝ ∞ (fun tp : ℝ × (A × B) =>
      lamAmb (φ (σ tp)) (fderiv ℝ φ (σ tp) ((0 : A), tp.2.2))) (σ ⁻¹' U) :=
    lamAmb_contDiff.comp_contDiffOn (h1.prodMk h2)
  have hmain := integral_contDiffAt_of_open hWo hF (p₀ := p₀) fun t ht => hseg t ht
  apply hmain.congr_of_eventuallyEq
  have hnear : ∀ᶠ p in 𝓝 p₀, ∀ t ∈ Icc (0 : ℝ) 1, (t, p) ∈ σ ⁻¹' U := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    exact (continuous_swap.tendsto (p₀, t)).eventually (hWo.mem_nhds (hseg t ht))
  filter_upwards [hnear] with p hp
  unfold lineAction
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have hpt : ContDiffAt ℝ ∞ φ (p.1, t • p.2) := hφU _ (hp t ht)
  have hin : HasDerivAt (fun s : ℝ => ((p.1, s • p.2) : A × B)) ((0 : A), p.2) t := by
    have := (hasDerivAt_const t p.1).prodMk ((hasDerivAt_id' t).smul_const p.2)
    simpa only [one_smul] using this
  have hd := (hpt.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t hin
  have hd' : deriv (fun s => φ (p.1, s • p.2)) t = fderiv ℝ φ (p.1, t • p.2) ((0 : A), p.2) :=
    hd.deriv
  show lamAmb (φ (p.1, t • p.2)) (deriv (fun s => φ (p.1, s • p.2)) t) =
    lamAmb (φ (p.1, t • p.2)) (fderiv ℝ φ (p.1, t • p.2) ((0 : A), p.2))
  rw [hd']

theorem radialAct_contDiffAt (hh : 0 < h₂) (hh2 : h₂ < 1 / 2)
    {p₀ : Affine (q + 2) × Fibre (q + 2)}
    (hp₀ : p₀ ∈ BranchSmall.VT.tube (parameters q) (transferHeight h₂)) :
    ContDiffAt ℝ ∞ (radialAct q h₂) p₀ := by
  have hb0 : 0 < transferHeight h₂ := transferHeight_pos hh
  have hb : transferHeight h₂ < 1 / 2 := transferHeight_lt hh2
  have hUo : IsOpen {y : Affine (q + 2) × Fibre (q + 2) | ∀ᶠ y' in 𝓝 y,
      ContDiffAt ℝ ∞ (BranchSmall.VT.transferMap (parameters q) (transferHeight h₂)) y'} :=
    isOpen_iff_mem_nhds.2 fun y hy => eventually_eventually_nhds.2 hy
  refine segment_lineAction_contDiffAt hUo (fun y hy => hy.self_of_nhds) fun t ht => ?_
  refine transferMap_eventually_contDiffAt q hb0 hb _ ⟨hp₀.1, ?_⟩
  change Real.pi * BranchSmall.VT.wsq (BranchSmall.VT.toC (t • p₀.2)) < transferHeight h₂
  rw [wsq_toC_smul]
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hw0 := BranchSmall.VT.wsq_nonneg (BranchSmall.VT.toC p₀.2)
  have := hp₀.2
  have hle : Real.pi * (t ^ 2 * BranchSmall.VT.wsq (BranchSmall.VT.toC p₀.2)) ≤
      Real.pi * BranchSmall.VT.wsq (BranchSmall.VT.toC p₀.2) :=
    mul_le_mul_of_nonneg_left (mul_le_of_le_one_left hw0 ht2) Real.pi_pos.le
  linarith

/-- **Smoothness of the lift phase on the transfer tube.** -/
theorem liftPhase_contMDiffOn_aux (hh : 0 < h₂) (hh2 : h₂ < 1 / 2) :
    ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × Fibre (q + 2)) 𝓘(ℝ, ℝ) ∞
      (fun x : Surface q × Fibre (q + 2) => liftPhase q h₂ x.1 x.2)
      (BranchSmall.transferDomain q (transferHeight h₂)) := by
  have heq : (fun x : Surface q × Fibre (q + 2) => liftPhase q h₂ x.1 x.2) =
      fun x => radialAct q h₂ (BranchSmall.surfaceIncl q x) := by
    funext x
    simp only [liftPhase, zeroPhase_eq_zero, zero_add]
    rfl
  rw [heq]
  intro x hx
  have hR := radialAct_contDiffAt hh hh2 (BranchSmall.surfaceIncl_mem_tube q hx)
  exact ((hR.contMDiffAt.comp x (BranchSmall.surfaceIncl_contMDiff q x))).contMDiffWithinAt

end SymplecticPacking.BranchLargeHigh.Two.LiftSmooth
