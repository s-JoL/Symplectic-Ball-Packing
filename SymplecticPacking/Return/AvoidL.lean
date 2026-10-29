import SymplecticPacking.Return.ReturnFlow
import SymplecticPacking.Return.BallChart

/-!
# Avoiding `L` and the composite map

`sec:rtc`, avoiding `L` by equivariant injectivity, and the ball chart
(Proposition prop:rtc-avoid, Lemma lem:rtc-ball-chart, at the level of representatives).

The composite `𝒯 = ψ₁⁻¹ ∘ pr ∘ τ₁ ∘ ι` on unit representatives `x = (Z, U)` of
`N_{p ≤ h}` (`NDom h`: `‖Z‖ = 1`, `F(Z) = 0`, `π|U|² ≤ h`, `h < d_n`) is `compositeT dn h`; the
transport is run with the bound `w = h/(d_n − h)` on `|W|²` (`injection_normW_le`).

* `compositeT_nsq`: `𝒯(x)` is a unit vector.
* `compositeT_gauge`, `compositeT_equivariant`: `𝒯(cZ, c³U) = c 𝒯(Z,U)`, `𝒯(gZ, U) = g 𝒯(Z,U)`.
* `compositeT_inj_mod_gauge`: injectivity modulo gauge (so `𝒯` is injective as a map
  `N_{p ≤ h} → CP²`).
* `compositeT_pullback`: `𝒯^* ω_FS = ι^* Ω_E` on smooth families (with prop:rtc-central this
  is `Ω₀`).
* **`avoid_L`**: if `Z₀ ≠ 0` then `𝒯(x)₀ ≠ 0` (and `𝒯(x) ≠ [1:0:0]`), by the fixed-point
  argument; `avoid_L_compact`: a uniform lower bound for `|𝒯(x)₀|` on compact sets.
* `compositeBall_mem`: the ball-chart composite lands in the open ball `π‖y‖² < 1`.
-/

noncomputable section

namespace SymplecticPacking.Return

open Complex ComplexConjugate Filter Topology Set Metric
open SymplecticPacking.Forms (Form2 pull2 pull2_apply pull2_comp_apply)
open scoped Real ContDiff

/-- Unit representatives of `N_{p ≤ h}`. -/
def NDom (h : ℝ) : Set (C3 × ℂ) := {x | nsq x.1 = 1 ∧ Fpoly x.1 = 0 ∧ pN x.2 ≤ h}

/-- The bound `w = h/(d_n − h)` for `|W|²` on `ι(N_{p ≤ h})`. -/
def wOf (dn h : ℝ) : ℝ := h / (dn - h)

/-- **The composite** `𝒯 = ψ₁⁻¹ ∘ pr ∘ τ₁ ∘ ι` on representatives. -/
def compositeT (dn h : ℝ) (x : C3 × ℂ) : C3 :=
  returnFlowInv dn 1 (transport dn (wOf dn h) 1 (injection dn x)).1

/-- The ball-chart composite `b_ball ∘ 𝒯`. -/
def compositeBall (dn h : ℝ) (x : C3 × ℂ) : ℂ × ℂ := ballChart (compositeT dn h x)

section

variable {dn h : ℝ} (hdn : 0 < dn) (hdn3 : dn < 1 / 3) (hh : h < dn)
include hdn hdn3

omit hdn hdn3 in
lemma injection_mem (hh : h < dn) {x : C3 × ℂ} (hx : x ∈ NDom h) :
    nsq (injection dn x).1 = 1 ∧ Fpoly (injection dn x).1 = 0 ∧
      normSq (injection dn x).2 ≤ wOf dn h :=
  ⟨hx.1, hx.2.1, injection_normW_le hh hx.2.2⟩

lemma compositeT_nsq (x : C3 × ℂ) : nsq (compositeT dn h x) = nsq x.1 := by
  rw [compositeT, nsq_returnFlowInv hdn3.le, nsq_transport hdn hdn3.le]; rfl

include hh in
/-- On `X₁`, `τ₁(ι x)` is a graph point: `W = F(Z)`. -/
lemma transport_injection_graph {x : C3 × ℂ} (hx : x ∈ NDom h) :
    transport dn (wOf dn h) 1 (injection dn x) =
      graph (transport dn (wOf dn h) 1 (injection dn x)).1 := by
  obtain ⟨h1, h2, h3⟩ := injection_mem hh hx
  have := (transport_mem hdn hdn3.le h1 h2 h3 (right_mem_Icc.mpr zero_le_one)).2.1
  rw [graph, this]; push_cast; rw [one_mul]

/-- `g`-equivariance of `𝒯`. -/
theorem compositeT_equivariant (x : C3 × ℂ) :
    compositeT dn h (cubeRoot x.1, x.2) = cubeRoot (compositeT dn h x) := by
  rw [compositeT, injection_equivariant, transport_equivariant hdn hdn3.le,
    returnFlowInv_equivariant hdn3.le]
  rfl

/-- Gauge equivariance of `𝒯`. -/
theorem compositeT_gauge (x : C3 × ℂ) {c : ℂ} (hc : conj c * c = 1) :
    compositeT dn h (c • x.1, c ^ 3 * x.2) = c • compositeT dn h x := by
  rw [compositeT, injection_wellDefined hc,
    show ((c • x.1, c ^ 3 * (injection dn (x.1, x.2)).2) : C3 × ℂ) =
      (c • (injection dn x).1, c ^ 3 * (injection dn x).2) from rfl,
    transport_gaugeEquiv hdn hdn3.le _ _ _ hc,
    returnFlowInv_gaugeEquiv hdn3.le _ _ hc]
  rfl

omit hdn hdn3 in
lemma NDom_gauge {x : C3 × ℂ} (hx : x ∈ NDom h) {c : ℂ} (hc : conj c * c = 1) :
    ((c • x.1, c ^ 3 * x.2) : C3 × ℂ) ∈ NDom h :=
  ⟨by rw [nsq_smul_of_unit _ hc]; exact hx.1, by rw [Fpoly_smul, hx.2.1, mul_zero],
    by rw [pN_smul_of_unit (unit_pow hc 3)]; exact hx.2.2⟩

omit hdn hdn3 in
lemma NDom_cubeRoot {x : C3 × ℂ} (hx : x ∈ NDom h) : ((cubeRoot x.1, x.2) : C3 × ℂ) ∈ NDom h :=
  ⟨by rw [nsq_cubeRoot]; exact hx.1, by rw [Fpoly_cubeRoot]; exact hx.2.1, hx.2.2⟩

include hh in
/-- **Injectivity modulo gauge**: `𝒯(x) = μ 𝒯(x')` with `|μ| = 1` forces `x = μ · x'`. -/
theorem compositeT_inj_mod_gauge {x x' : C3 × ℂ} (hx : x ∈ NDom h) (hx' : x' ∈ NDom h)
    {μ : ℂ} (hμ : conj μ * μ = 1) (he : compositeT dn h x = μ • compositeT dn h x') :
    x = (μ • x'.1, μ ^ 3 * x'.2) := by
  set x'' : C3 × ℂ := (μ • x'.1, μ ^ 3 * x'.2)
  have hx'' : x'' ∈ NDom h := NDom_gauge hx' hμ
  rw [← compositeT_gauge hdn hdn3 x' hμ] at he
  have h1 := returnFlowInv_injective hdn3.le 1 he
  have h2 : transport dn (wOf dn h) 1 (injection dn x) =
      transport dn (wOf dn h) 1 (injection dn x'') := by
    rw [transport_injection_graph hdn hdn3 hh hx, transport_injection_graph hdn hdn3 hh hx'', h1]
  have h3 := transport_injective hdn hdn3.le _ 1 h2
  have hlt : ∀ y ∈ NDom h, pN y.2 < dn := fun y hy => lt_of_le_of_lt hy.2.2 hh
  have h4 := congrArg (injectionInv dn) h3
  simp only [injection, injectionInv, injWinv_injW (hlt x hx), injWinv_injW (hlt x'' hx'')] at h4
  exact h4

include hh in
/-- **Proposition prop:rtc-avoid** (fixed-point argument): if `x ∈ N_{p ≤ h}` lies off the
fibres over `C ∩ L` (`Z₀ ≠ 0`), then `𝒯(x) ∉ L ∪ {[1:0:0]}`: `𝒯(x)₀ ≠ 0` and
`(𝒯(x)₁, 𝒯(x)₂) ≠ 0`. -/
theorem avoid_L {x : C3 × ℂ} (hx : x ∈ NDom h) (h0 : x.1 0 ≠ 0) :
    compositeT dn h x 0 ≠ 0 ∧ ¬(compositeT dn h x 1 = 0 ∧ compositeT dn h x 2 = 0) := by
  set Y := compositeT dn h x
  have hY : nsq Y = 1 := (compositeT_nsq hdn hdn3 x).trans hx.1
  suffices hfix : ¬(Y 0 = 0 ∨ (Y 1 = 0 ∧ Y 2 = 0)) by
    push Not at hfix
    exact ⟨hfix.1, fun h => hfix.2 h.1 h.2⟩
  intro hfix
  obtain ⟨μ, hμ⟩ := (fixed_CP2 Y).mpr hfix
  -- `|μ| = 1`
  have hμ1 : conj μ * μ = 1 := by
    have h1 := congrArg nsq hμ
    rw [nsq_cubeRoot, nsq_smul, hY, mul_one] at h1
    rw [← ofReal_normSq', ← h1, ofReal_one]
  -- `𝒯(gx) = g𝒯(x) = μ 𝒯(x)`, so `gx = μ · x`
  have he : compositeT dn h (cubeRoot x.1, x.2) = μ • compositeT dn h x := by
    rw [compositeT_equivariant hdn hdn3, hμ]
  have hgx := compositeT_inj_mod_gauge hdn hdn3 hh (NDom_cubeRoot hx) hx hμ1 he
  have hZ : x.1 ≠ 0 := ne_zero_of_nsq_eq_one hx.1
  have := (fixed_N hx.2.1 hZ x.2).mp ⟨μ, congrArg Prod.fst hgx, congrArg Prod.snd hgx⟩
  exact h0 this

include hh in
/-- **The ball chart lands in the open ball**: `π ‖b_ball(𝒯(x))‖² = 1 − |𝒯(x)₀|² < 1`. -/
theorem compositeBall_mem {x : C3 × ℂ} (hx : x ∈ NDom h) (h0 : x.1 0 ≠ 0) :
    π * nsq2 (compositeBall dn h x) < 1 :=
  ballChart_norm_lt _ ((compositeT_nsq hdn hdn3 x).trans hx.1) (avoid_L hdn hdn3 hh hx h0).1

/-! ### Smoothness and the pullback identity -/

omit hdn hdn3 in
lemma contDiffAt_injection {x : C3 × ℂ} (hx : pN x.2 < dn) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (injection dn) x := by
  have hp : ContDiff ℝ n (fun y : C3 × ℂ => pN y.2) :=
    contDiff_const.mul (contDiff_normSq'.comp contDiff_snd)
  have hs : ContDiffAt ℝ n (fun y : C3 × ℂ => Real.sqrt (dn - pN y.2)) x :=
    (contDiff_const.sub hp).contDiffAt.sqrt (by linarith)
  have hsp : Real.sqrt (dn - pN x.2) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  have hq : ContDiffAt ℝ n (fun y : C3 × ℂ => ((Real.sqrt π / Real.sqrt (dn - pN y.2) : ℝ) : ℂ))
      x := ofRealCLM.contDiff.contDiffAt.comp x (contDiffAt_const.div hs hsp)
  exact contDiffAt_fst.prodMk (hq.mul contDiffAt_snd)

include hh in
/-- **`𝒯^* ω_FS = ι^* Ω_E`** on every smooth family of points of `N_{p ≤ h}`
(Propositions prop:rtc-transport, prop:rtc-return and `γ^*Ω_E = ω_1`). Combined with
Proposition prop:rtc-central (`ι^*Ω_E = Ω₀`) this is `𝒯^* ω_FS = Ω₀`. -/
theorem compositeT_pullback {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ₀ : E → C3 × ℂ} (hφ : ContDiff ℝ ∞ φ₀) (hφD : ∀ x, φ₀ x ∈ NDom h) :
    pull2 (fun x => compositeT dn h (φ₀ x)) (omegaS dn 0) =
      pull2 (fun x => injection dn (φ₀ x)) (OmegaE dn) := by
  have hι : ContDiff ℝ ∞ (fun x => injection dn (φ₀ x)) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    exact (contDiffAt_injection (lt_of_le_of_lt (hφD x).2.2 hh)).comp x hφ.contDiffAt
  set w := wOf dn h
  have hτ : ContDiff ℝ ∞ (fun x => transport dn w 1 (injection dn (φ₀ x))) :=
    (transport_smooth hdn hdn3.le w).comp (contDiff_const.prodMk hι)
  set ψ : E → C3 := fun x => (transport dn w 1 (injection dn (φ₀ x))).1 with hψ
  have hψs : ContDiff ℝ ∞ ψ := contDiff_fst.comp hτ
  have hψu : ∀ x, nsq (ψ x) = 1 := fun x =>
    ((nsq_transport hdn hdn3.le w 1 _).trans (hφD x).1)
  have hstep1 := returnFlowInv_pullback hdn.le hdn3 hψs hψu (right_mem_Icc.mpr zero_le_one)
  have hgraph : graph ∘ ψ = fun x => transport dn w 1 (injection dn (φ₀ x)) := by
    funext x
    exact (transport_injection_graph hdn hdn3 hh (hφD x)).symm
  have hstep2 : pull2 ψ (omegaS dn 1) = pull2 (graph ∘ ψ) (OmegaE dn) := by
    funext x
    rw [pull2_comp_apply (hψs.differentiable (by simp) x) ((contDiff_graph (n := 1)).differentiable
      one_ne_zero _)]
    ext v w'
    simp only [pull2_apply]
    rw [omegaS_graph dn 1 (ne_zero_of_nsq_eq_one (hψu x)), one_mul]
    rfl
  have hstep3 := transport_pullback hdn hdn3.le hι (fun x => (injection_mem hh (hφD x)).1)
    (fun x => (injection_mem hh (hφD x)).2.1) (fun x => (injection_mem hh (hφD x)).2.2)
    (right_mem_Icc.mpr zero_le_one)
  change pull2 (fun x => returnFlowInv dn 1 (ψ x)) (omegaS dn 0) = _
  rw [hstep1, hstep2, hgraph, hstep3]

/-! ### A uniform lower bound for `|𝒯(x)₀|` on compact sets -/

omit hdn hdn3 in
lemma continuousOn_injection : ContinuousOn (injection dn) {x : C3 × ℂ | pN x.2 < dn} :=
  fun x hx => (contDiffAt_injection hx (n := 0)).continuousAt.continuousWithinAt

include hh in
lemma continuousOn_compositeT : ContinuousOn (compositeT dn h) {x : C3 × ℂ | pN x.2 < dn} := by
  have h1 : Continuous (fun y : C3 × ℂ => returnFlowInv dn 1 (transport dn (wOf dn h) 1 y).1) :=
    ((returnFlowInv_smooth hdn3.le).continuous.comp (continuous_const.prodMk
      (continuous_fst.comp ((transport_smooth hdn hdn3.le _).continuous.comp
        (continuous_const.prodMk continuous_id)))))
  exact h1.comp_continuousOn continuousOn_injection

include hh in
/-- **The last claim of prop:rtc-avoid**: on every compact `K ⊆ N_{p ≤ h}` off the fibres
over `C ∩ L`, `|𝒯(x)₀|` is bounded below by a positive constant. -/
theorem avoid_L_compact {K : Set (C3 × ℂ)} (hK : IsCompact K) (hKD : K ⊆ NDom h)
    (hK0 : ∀ x ∈ K, x.1 0 ≠ 0) : ∃ δ > 0, ∀ x ∈ K, δ ≤ ‖compositeT dn h x 0‖ := by
  rcases K.eq_empty_or_nonempty with hKe | hKn
  · exact ⟨1, one_pos, by simp [hKe]⟩
  have hc : ContinuousOn (fun x => ‖compositeT dn h x 0‖) K :=
    ((continuousOn_pi.mp ((continuousOn_compositeT hdn hdn3 hh).mono
      fun x hx => lt_of_le_of_lt (hKD hx).2.2 hh)) 0).norm
  obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hKn hc
  refine ⟨‖compositeT dn h x₀ 0‖, norm_pos_iff.mpr (avoid_L hdn hdn3 hh (hKD hx₀) (hK0 x₀ hx₀)).1,
    fun x hx => hmin hx⟩

end

end SymplecticPacking.Return
