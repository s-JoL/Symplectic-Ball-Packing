import SymplecticPacking.HighDim.Comparator.Poly
import SymplecticPacking.HighDim.Comparator.Isotopy
import SymplecticPacking.HighDim.Comparator.RealiseGen

/-!
# Supporting lemmas for `liftFamily_estimate` (supplement S-thm:plc-lift (c))

* Global integral curves of jointly smooth, *spatially* compactly supported time-dependent fields
  (no compact support in time is assumed): existence and uniqueness, so `Return.flow` is the
  unique integral curve (`flow_eq_of_sol`). This applies to the field of the planar generator
  `RealiseGen.planarGen`, whose contract `PlanarSpec` has spatial support only.
* The planar flow of the rescaled, reclocked generator
  `g(t,u) = c S'(t) ℓ B(c S(t), u/√ℓ)` is `√ℓ · Φ^B_{c S(t)}(u/√ℓ)` (`flow_rescale`).
* Fixed points outside the support and invariance of discs (`flow_fix`, `flow_disc`).
* Slice facts: soft-min bounds `L − ζ/2 ≤ ℓ ≤ L − δ₀`, the cutoff is `1` on long slices of `Δ`,
  long slices lie in `bigParams`, Lipschitz bound of `F` along a slice.
* `liftFamily_estimate_aux`: the estimate, stated with `liftFamily` unfolded.
-/

noncomputable section

namespace SymplecticPacking.HighDim.LiftEst

open Set Filter Topology
open OAI.PackingSufficiencySupport.Hamiltonian (radialArea)
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff NNReal

/-! ### Global flows of spatially supported fields -/

section ode

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

/-- Time cutoff equal to `1` on `[-n, n]`, supported in `[-(n+1), n+1]`. -/
def tcut (n s : ℝ) : ℝ := Real.smoothTransition (n + 1 + s) * Real.smoothTransition (n + 1 - s)

theorem tcut_eq_one {n s : ℝ} (h : |s| ≤ n) : tcut n s = 1 := by
  unfold tcut
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
  · linarith [le_abs_self s]
  · linarith [neg_abs_le s]

theorem tcut_eq_zero {n s : ℝ} (h : s ∉ Icc (-(n + 1)) (n + 1)) : tcut n s = 0 := by
  unfold tcut
  rcases not_and_or.mp h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (show n + 1 + s ≤ 0 by linarith [not_le.mp h]),
      zero_mul]
  · rw [Real.smoothTransition.zero_of_nonpos (show n + 1 - s ≤ 0 by linarith [not_le.mp h]),
      mul_zero]

theorem tcut_smooth (n : ℝ) : ContDiff ℝ ∞ (tcut n) := by
  unfold tcut
  exact ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).comp
    (contDiff_const.add contDiff_id)).mul
    ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).comp
      (contDiff_const.sub contDiff_id))

/-- The time-cut field. -/
def cutV (V : ℝ → E → E) (n s : ℝ) (x : E) : E := tcut n s • V s x

theorem cutV_eq (V : ℝ → E → E) {n s : ℝ} (h : |s| ≤ n) (x : E) : cutV V n s x = V s x := by
  simp [cutV, tcut_eq_one h]

variable {V : ℝ → E → E} (hV : ContDiff ℝ ∞ (fun p : ℝ × E => V p.1 p.2))
  {r : ℝ} (hr : ∀ s x, r ≤ ‖x‖ → V s x = 0)
include hV hr

theorem cutV_cs (n : ℝ) : Return.CSField (cutV V n) := by
  refine ⟨((tcut_smooth n).comp contDiff_fst).smul hV, ?_⟩
  refine HasCompactSupport.intro (K := Icc (-(n + 1)) (n + 1) ×ˢ Metric.closedBall (0 : E) r)
    (isCompact_Icc.prod (isCompact_closedBall 0 r)) ?_
  rintro ⟨s, x⟩ hp
  simp only [mem_prod, Metric.mem_closedBall, dist_zero_right, not_and_or, not_le] at hp
  show tcut n s • V s x = 0
  rcases hp with h | h
  · rw [tcut_eq_zero h, zero_smul]
  · rw [hr s x h.le, smul_zero]

theorem eqOn_of_sol {n : ℝ} (hn : 0 < n) {x : E} {u : ℝ → E}
    (hu0 : u 0 = x) (hu : ∀ t ∈ Ioo (-n) n, HasDerivAt u (V t (u t)) t)
    (huc : ContinuousOn u (Icc (-n) n)) :
    EqOn u (fun t => Return.flow (cutV V n) t x) (Icc (-n) n) := by
  have hcs := cutV_cs hV hr n
  obtain ⟨K, hK⟩ := hcs.lipschitz_slice
  have hcut : ∀ t ∈ Ioo (-n) n, ∀ y, cutV V n t y = V t y := fun t ht y =>
    cutV_eq V (abs_le.mpr ⟨ht.1.le, ht.2.le⟩) y
  refine ODE_solution_unique_of_mem_Icc (v := cutV V n) (s := fun _ => univ) (K := K)
    (fun t _ => (hK t).lipschitzOnWith) ⟨by linarith, hn⟩ huc
    (fun t ht => by rw [hcut t ht]; exact hu t ht) (fun _ _ => mem_univ _)
    (hcs.flowFrom_continuous 0 x).continuousOn (fun t _ => hcs.flow_hasDerivAt x t)
    (fun _ _ => mem_univ _) (by rw [hu0]; exact (hcs.flow_zero x).symm)

theorem flow_cutV_agree {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) (x : E) :
    EqOn (fun t => Return.flow (cutV V N) t x) (fun t => Return.flow (cutV V n) t x)
      (Icc (-(n : ℝ)) n) := by
  have hcs := cutV_cs hV hr (N : ℝ)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  refine eqOn_of_sol hV hr hn' (hcs.flow_zero x) (fun t ht => ?_)
    (hcs.flowFrom_continuous 0 x).continuousOn
  have h := hcs.flow_hasDerivAt x t
  rwa [cutV_eq V (abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩)] at h

/-- The global solution, assembled from the time-cut flows. -/
def gsol (V : ℝ → E → E) (x : E) (s : ℝ) : E :=
  Return.flow (cutV V ((⌈|s|⌉₊ + 1 : ℕ) : ℝ)) s x

theorem gsol_isSol (x : E) : Return.IsSolFrom V 0 x (gsol V x) := by
  refine ⟨?_, fun s => ?_⟩
  · exact (cutV_cs hV hr _).flow_zero x
  · set M : ℕ := ⌈|s|⌉₊ + 2 with hM
    have hev : gsol V x =ᶠ[𝓝 s] fun s' => Return.flow (cutV V M) s' x := by
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds
        (show |s| < |s| + 1 by linarith)] with s' hs'
      have hc : ⌈|s'|⌉₊ ≤ ⌈|s|⌉₊ + 1 := by
        apply Nat.ceil_le.mpr
        push_cast
        linarith [Nat.le_ceil |s|]
      have h1 : |s'| ≤ ((⌈|s'|⌉₊ + 1 : ℕ) : ℝ) := by
        push_cast; linarith [Nat.le_ceil |s'|]
      have := flow_cutV_agree hV hr (n := ⌈|s'|⌉₊ + 1) (N := M) (by omega) (by omega) x
        (abs_le.mp h1)
      exact this.symm
    have hd := (cutV_cs hV hr (M : ℝ)).flow_hasDerivAt x s
    have hsM : |s| ≤ (M : ℝ) := by
      rw [hM]; push_cast; linarith [Nat.le_ceil |s|]
    rw [cutV_eq V hsM, ← hev.eq_of_nhds] at hd
    exact hd.congr_of_eventuallyEq hev

theorem existsUnique_sol (x : E) : ∃! u : ℝ → E, Return.IsSolFrom V 0 x u := by
  refine ⟨gsol V x, gsol_isSol hV hr x, fun u hu => ?_⟩
  funext t
  have hn : (0 : ℝ) < ((⌈|t|⌉₊ + 1 : ℕ) : ℝ) := by positivity
  have ht : t ∈ Icc (-((⌈|t|⌉₊ + 1 : ℕ) : ℝ)) ((⌈|t|⌉₊ + 1 : ℕ) : ℝ) := by
    apply abs_le.mp; push_cast; linarith [Nat.le_ceil |t|]
  have hcont : ∀ w : ℝ → E, Return.IsSolFrom V 0 x w → ContinuousOn w (Icc (-((⌈|t|⌉₊ + 1 : ℕ) : ℝ))
      ((⌈|t|⌉₊ + 1 : ℕ) : ℝ)) := fun w hw =>
    (continuous_iff_continuousAt.mpr fun s => (hw.2 s).continuousAt).continuousOn
  have h1 := eqOn_of_sol hV hr hn hu.1 (fun s _ => hu.2 s) (hcont u hu) ht
  have h2 := eqOn_of_sol hV hr hn (gsol_isSol hV hr x).1 (fun s _ => (gsol_isSol hV hr x).2 s)
    (hcont _ (gsol_isSol hV hr x)) ht
  rw [h1, h2]

/-- `Return.flow` is the unique global integral curve. -/
theorem flow_eq_of_sol {x : E} {u : ℝ → E} (hu : Return.IsSolFrom V 0 x u) (t : ℝ) :
    Return.flow V t x = u t := by
  unfold Return.flow Return.flowFrom
  rw [dif_pos (existsUnique_sol hV hr x), Explicit.the_eq (existsUnique_sol hV hr x) hu]

theorem flow_isSol (x : E) : Return.IsSolFrom V 0 x (fun t => Return.flow V t x) := by
  have : (fun t => Return.flow V t x) = gsol V x :=
    funext fun t => flow_eq_of_sol hV hr (gsol_isSol hV hr x) t
  rw [this]; exact gsol_isSol hV hr x

end ode

/-! ### Planar fields -/

/-- The planar field of `g` (convention `ι_X ω = −dg`); definitionally `HighDim.planarVF g`
and `RealiseGen.planarVF B y` for `g = B y`. -/
def pvf (g : ℝ → ℝ × ℝ → ℝ) (t : ℝ) (u : ℝ × ℝ) : ℝ × ℝ :=
  (-(fderiv ℝ (g t) u (0, 1)), fderiv ℝ (g t) u (1, 0))

theorem radialArea_eq' (u : ℝ × ℝ) : radialArea u = Real.pi * (u.1 ^ 2 + u.2 ^ 2) := rfl

theorem radialArea_nonneg' (u : ℝ × ℝ) : 0 ≤ radialArea u := by
  rw [radialArea_eq']; positivity

theorem continuous_radialArea : Continuous radialArea := by
  have : radialArea = fun u : ℝ × ℝ => Real.pi * (u.1 ^ 2 + u.2 ^ 2) := rfl
  rw [this]; fun_prop

theorem norm_sq_le_radialArea (u : ℝ × ℝ) : ‖u‖ ^ 2 ≤ radialArea u := by
  rw [radialArea_eq', Prod.norm_def]
  have h1 : ‖u.1‖ ^ 2 = u.1 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have h2 : ‖u.2‖ ^ 2 = u.2 ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  rcases le_total ‖u.1‖ ‖u.2‖ with h | h
  · rw [max_eq_right h, h2]
    nlinarith [sq_nonneg u.1, sq_nonneg u.2]
  · rw [max_eq_left h, h1]
    nlinarith [sq_nonneg u.1, sq_nonneg u.2]

theorem radialArea_smul (a : ℝ) (u : ℝ × ℝ) : radialArea (a • u) = a ^ 2 * radialArea u := by
  rw [radialArea_eq', radialArea_eq']
  simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem pvf_eq_zero {g : ℝ → ℝ × ℝ → ℝ} {t : ℝ} {u : ℝ × ℝ}
    (h : ∀ᶠ v in 𝓝 u, g t v = 0) : pvf g t u = 0 := by
  have : g t =ᶠ[𝓝 u] fun _ => 0 := h
  simp [pvf, this.fderiv_eq]

theorem pvf_smooth {g : ℝ → ℝ × ℝ → ℝ}
    (hg : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => g x.1 x.2)) :
    ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => pvf g x.1 x.2) := by
  have hf : ContDiff ℝ ∞ (Function.uncurry fun (p : ℝ × (ℝ × ℝ)) (v : ℝ × ℝ) => g p.1 v) :=
    hg.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hD : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => fderiv ℝ (g p.1) p.2) :=
    ContDiff.fderiv (f := fun (p : ℝ × (ℝ × ℝ)) (v : ℝ × ℝ) => g p.1 v) hf contDiff_snd
      (le_of_eq rfl)
  show ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) =>
    ((-(fderiv ℝ (g p.1) p.2 (0, 1)), fderiv ℝ (g p.1) p.2 (1, 0)) : ℝ × ℝ))
  exact (hD.clm_apply contDiff_const).neg.prodMk (hD.clm_apply contDiff_const)

/-- Radial support of `g` gives norm support of its field. -/
theorem pvf_support {g : ℝ → ℝ × ℝ → ℝ} {ρ : ℝ} (hg : ∀ t v, ρ < radialArea v → g t v = 0) :
    ∀ t u, Real.sqrt (max ρ 0) + 1 ≤ ‖u‖ → pvf g t u = 0 := by
  intro t u hu
  apply pvf_eq_zero
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
    (show Real.sqrt (max ρ 0) < ‖u‖ by linarith)] with v hv
  apply hg
  have h0 : 0 ≤ Real.sqrt (max ρ 0) := Real.sqrt_nonneg _
  have h1 : Real.sqrt (max ρ 0) ^ 2 < ‖v‖ ^ 2 := pow_lt_pow_left₀ hv h0 (by norm_num)
  rw [Real.sq_sqrt (le_max_right ρ 0)] at h1
  linarith [le_max_left ρ 0, norm_sq_le_radialArea v]

/-- A compactly supported planar field (time support `[0,1]`). -/
theorem pvf_cs {g : ℝ → ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => g x.1 x.2))
    {ρ : ℝ} (hρ : ∀ t v, ρ < radialArea v → g t v = 0)
    (ht : ∀ t, t ∉ Icc (0 : ℝ) 1 → ∀ v, g t v = 0) : Return.CSField (pvf g) := by
  refine ⟨pvf_smooth hg, ?_⟩
  refine HasCompactSupport.intro
    (K := Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : ℝ × ℝ) (Real.sqrt (max ρ 0) + 1))
    (isCompact_Icc.prod (isCompact_closedBall _ _)) ?_
  rintro ⟨t, u⟩ hp
  simp only [mem_prod, Metric.mem_closedBall, dist_zero_right, not_and_or, not_le] at hp
  show pvf g t u = 0
  rcases hp with h | h
  · exact pvf_eq_zero (Filter.Eventually.of_forall fun v => ht t h v)
  · exact pvf_support hρ t u h.le

/-! ### The rescaled, reclocked planar generator -/

section rescale

/-- `g(t,u) = c S'(t) ℓ B(c S(t), u/√ℓ)`. -/
def resc (B : ℝ → ℝ × ℝ → ℝ) (c ℓ : ℝ) (t : ℝ) (u : ℝ × ℝ) : ℝ :=
  c * deriv Real.smoothTransition t * ℓ *
    B (c * Real.smoothTransition t) ((Real.sqrt ℓ)⁻¹ • u)

theorem contDiff_derivS : ContDiff ℝ ∞ (deriv Real.smoothTransition) :=
  (contDiff_infty_iff_deriv.mp Real.smoothTransition.contDiff).2

variable {B : ℝ → ℝ × ℝ → ℝ} (hB : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => B x.1 x.2))

include hB in
theorem resc_smooth (c ℓ : ℝ) :
    ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => resc B c ℓ x.1 x.2) := by
  unfold resc
  exact ((contDiff_const.mul (contDiff_derivS.comp contDiff_fst)).mul contDiff_const).mul
    (hB.comp ((contDiff_const.mul
      ((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).comp contDiff_fst)).prodMk
      (contDiff_snd.const_smul _)))

theorem resc_time (c ℓ : ℝ) : ∀ t, t ∉ Icc (0 : ℝ) 1 → ∀ v, resc B c ℓ t v = 0 := by
  intro t ht v
  have h : t ≤ 0 ∨ 1 ≤ t := by
    rcases not_and_or.mp ht with h | h
    · exact Or.inl (not_le.mp h).le
    · exact Or.inr (not_le.mp h).le
  simp [resc, deriv_smoothTransition_eq_zero h]

theorem resc_radial {rB : ℝ} (hrB : ∀ s w, rB < radialArea w → B s w = 0) (c : ℝ) {ℓ : ℝ}
    (hℓ : 0 < ℓ) : ∀ t v, rB * ℓ < radialArea v → resc B c ℓ t v = 0 := by
  intro t v hv
  unfold resc
  rw [hrB _ _ ?_, mul_zero]
  rw [radialArea_smul, inv_pow, Real.sq_sqrt hℓ.le, inv_mul_eq_div, lt_div_iff₀ hℓ]
  exact hv

include hB in
/-- The field of the rescaled generator. -/
theorem pvf_resc (c : ℝ) {ℓ : ℝ} (hℓ : 0 < ℓ) (t : ℝ) (u : ℝ × ℝ) :
    pvf (resc B c ℓ) t u =
      (c * deriv Real.smoothTransition t * Real.sqrt ℓ) •
        pvf B (c * Real.smoothTransition t) ((Real.sqrt ℓ)⁻¹ • u) := by
  have hBs : ∀ s, Differentiable ℝ (B s) := fun s =>
    (hB.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  have hsq : Real.sqrt ℓ ≠ 0 := (Real.sqrt_pos.mpr hℓ).ne'
  have hk : ℓ * (Real.sqrt ℓ)⁻¹ = Real.sqrt ℓ := by
    rw [inv_eq_one_div, mul_one_div, div_eq_iff hsq, Real.mul_self_sqrt hℓ.le]
  have hfd : ∀ v, fderiv ℝ (resc B c ℓ t) u v =
      (c * deriv Real.smoothTransition t * Real.sqrt ℓ) *
        fderiv ℝ (B (c * Real.smoothTransition t)) ((Real.sqrt ℓ)⁻¹ • u) v := by
    intro v
    have h1 : HasFDerivAt (fun v : ℝ × ℝ => (Real.sqrt ℓ)⁻¹ • v)
        ((Real.sqrt ℓ)⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ)) u :=
      ((Real.sqrt ℓ)⁻¹ • ContinuousLinearMap.id ℝ (ℝ × ℝ)).hasFDerivAt
    have h2 := (((hBs (c * Real.smoothTransition t))
      ((Real.sqrt ℓ)⁻¹ • u)).hasFDerivAt.comp u h1).const_mul
        (c * deriv Real.smoothTransition t * ℓ)
    rw [show resc B c ℓ t = fun v => (c * deriv Real.smoothTransition t * ℓ) *
        (B (c * Real.smoothTransition t) ∘ fun v : ℝ × ℝ => (Real.sqrt ℓ)⁻¹ • v) v from rfl,
      h2.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
    linear_combination (c * deriv Real.smoothTransition t *
      fderiv ℝ (B (c * Real.smoothTransition t)) ((Real.sqrt ℓ)⁻¹ • u) v) * hk
  simp only [pvf]
  rw [hfd, hfd]
  ext <;> simp [smul_eq_mul]

include hB in
/-- **Rescaling.** The planar flow of `resc B c ℓ` is `√ℓ · Φ^B_{c S(t)}(u/√ℓ)`. -/
theorem flow_resc {rB : ℝ} (hrB : ∀ s w, rB < radialArea w → B s w = 0) (c : ℝ) {ℓ : ℝ}
    (hℓ : 0 < ℓ) (t : ℝ) (w : ℝ × ℝ) :
    Return.flow (pvf (resc B c ℓ)) t (Real.sqrt ℓ • w) =
      Real.sqrt ℓ • Return.flow (pvf B) (c * Real.smoothTransition t) w := by
  have hsupB := pvf_support (g := B) hrB
  have hσ := flow_isSol (pvf_smooth hB) hsupB w
  have hsupg := pvf_support (resc_radial hrB c hℓ)
  have hsq : Real.sqrt ℓ ≠ 0 := (Real.sqrt_pos.mpr hℓ).ne'
  refine flow_eq_of_sol (pvf_smooth (resc_smooth hB c ℓ)) hsupg
    (u := fun t => Real.sqrt ℓ • Return.flow (pvf B) (c * Real.smoothTransition t) w)
    ⟨?_, fun t => ?_⟩ t
  · show Real.sqrt ℓ • Return.flow (pvf B) (c * Real.smoothTransition 0) w = Real.sqrt ℓ • w
    rw [Real.smoothTransition.zero, mul_zero]
    exact congrArg _ hσ.1
  · have hS : HasDerivAt (fun t => c * Real.smoothTransition t)
        (c * deriv Real.smoothTransition t) t :=
      (((Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).differentiable
        (by simp) t).hasDerivAt).const_mul c
    have h1 := (HasDerivAt.scomp t (hσ.2 (c * Real.smoothTransition t)) hS).const_smul
      (Real.sqrt ℓ)
    rw [pvf_resc hB c hℓ, inv_smul_smul₀ hsq]
    convert h1 using 1
    · funext s; rfl
    · simp only [smul_smul]; congr 1; ring

end rescale

/-! ### Fixed points and discs -/

/-- A point near which the generator vanishes at all times is fixed by the flow. -/
theorem flow_fix {g : ℝ → ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => g x.1 x.2))
    {ρ : ℝ} (hρ : ∀ t v, ρ < radialArea v → g t v = 0) {v : ℝ × ℝ} (hv : ρ < radialArea v)
    (t : ℝ) : Return.flow (pvf g) t v = v := by
  refine flow_eq_of_sol (pvf_smooth hg) (pvf_support hρ) (u := fun _ => v)
    ⟨rfl, fun s => ?_⟩ t
  have : pvf g s v = 0 := by
    apply pvf_eq_zero
    filter_upwards [(isOpen_lt continuous_const continuous_radialArea).mem_nhds hv] with v' hv'
    exact hρ s v' hv'
  rw [this]; exact hasDerivAt_const s v

/-- Discs of capacity `≥ ρ` are invariant. -/
theorem flow_disc {g : ℝ → ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => g x.1 x.2))
    {ρ : ℝ} (hρ : ∀ t v, ρ < radialArea v → g t v = 0)
    (ht : ∀ t, t ∉ Icc (0 : ℝ) 1 → ∀ v, g t v = 0) {L : ℝ} (hL : ρ ≤ L) (t : ℝ)
    {u : ℝ × ℝ} (hu : radialArea u ≤ L) : radialArea (Return.flow (pvf g) t u) ≤ L := by
  by_contra hcon
  push_neg at hcon
  have hcs := pvf_cs hg hρ ht
  have hfix := flow_fix hg hρ (lt_of_le_of_lt hL hcon) t
  have := hcs.flow_injective t hfix
  rw [this] at hcon
  linarith

/-- With a nonpositive length the generator is constant in `u` and its flow is the identity. -/
theorem flow_resc_nonpos (B : ℝ → ℝ × ℝ → ℝ) (c : ℝ) {ℓ : ℝ} (hℓ : ℓ ≤ 0) (t : ℝ)
    (u : ℝ × ℝ) : Return.flow (pvf (resc B c ℓ)) t u = u := by
  have hz : pvf (resc B c ℓ) = fun _ _ => 0 := by
    funext s v
    have hsq : Real.sqrt ℓ = 0 := Real.sqrt_eq_zero'.mpr hℓ
    have : resc B c ℓ s = fun _ => resc B c ℓ s 0 := by
      funext v'; simp [resc, hsq]
    simp only [pvf]
    rw [this]; simp
  rw [hz]
  exact flow_eq_of_sol (V := fun (_ : ℝ) (_ : ℝ × ℝ) => (0 : ℝ × ℝ)) contDiff_const
    (r := 0) (fun _ _ _ => rfl) (u := fun _ => u) ⟨rfl, fun s => hasDerivAt_const s u⟩ t

/-! ### Slice data -/

section slice

open RealiseGen

variable {m q : ℕ}

/-- `sliceBase j p` (the other moments, `j`-th entry `0`), unfolded. -/
abbrev sb (j : Fin m) (p : Moments m) : Moments m := fun i => if i = j then 0 else p i

theorem sb_self (j : Fin m) (p : Moments m) : sb j p j = 0 := if_pos rfl

theorem sb_ne {i j : Fin m} (h : i ≠ j) (p : Moments m) : sb j p i = p i := if_neg h

theorem update_sb (j : Fin m) (p : Moments m) (x : ℝ) :
    Function.update (sb j p) j x = Function.update p j x := by
  funext i
  by_cases h : i = j
  · subst h; simp
  · rw [Function.update_of_ne h, Function.update_of_ne h, sb_ne h]

theorem faceLen_sb (Δ : Polytope m q) (j : Fin m) (ν : Fin q) (p : Moments m) :
    faceLen Δ j ν (sb j p) = (Δ.ℓ ν - ∑ i, (if i = j then 0 else Δ.b ν i * p i)) / Δ.b ν j := by
  unfold faceLen
  congr 2
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i = j
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, sb_ne h]

theorem sliceLen_le_faceLen (Δ : Polytope m q) (j : Fin m) (p : Moments m) {ν : Fin q}
    (hν : 0 < Δ.b ν j) : Δ.sliceLen j p ≤ faceLen Δ j ν (sb j p) := by
  rw [faceLen_sb]
  exact ciInf_le (Set.finite_range _).bddBelow (⟨ν, hν⟩ : {ν : Fin q // 0 < Δ.b ν j})

/-- A summand of the soft minimum. -/
def softTerm (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) (y : Moments m)
    (ν : Fin q) : ℝ :=
  if 0 < Δ.b ν j then Real.exp (-faceLen Δ j ν y / softTemp q F j e) else 0

theorem softLen_eq (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) (y : Moments m) :
    softLen Δ F j e y =
      -softTemp q F j e * Real.log (∑ ν, softTerm Δ F j e y ν) - softShift F j e := rfl

theorem softTerm_nonneg (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) (y : Moments m)
    (ν : Fin q) : 0 ≤ softTerm Δ F j e y ν := by
  unfold softTerm; split_ifs <;> positivity

variable {Δ : Polytope m q} {F : PolyFn m} {j : Fin m} {e : ℝ}

/-- `ℓ ≤ L`. -/
theorem softLen_le (hΔ : Δ.Spec) (he : 0 < e) (p : Moments m) :
    softLen Δ F j e (sb j p) ≤ Δ.sliceLen j p := by
  have hs := softTemp_pos (q := q) F j he
  have hδ := softShift_pos F j he
  obtain ⟨ν0, hν0⟩ := hΔ.bounded_dir j
  haveI : Nonempty {ν : Fin q // 0 < Δ.b ν j} := ⟨⟨ν0, hν0⟩⟩
  unfold Polytope.sliceLen
  refine le_ciInf fun ν => ?_
  rw [← faceLen_sb]
  have hterm : Real.exp (-faceLen Δ j ν (sb j p) / softTemp q F j e) ≤
      ∑ ν', softTerm Δ F j e (sb j p) ν' := by
    have := Finset.single_le_sum (f := softTerm Δ F j e (sb j p))
      (fun ν' _ => softTerm_nonneg Δ F j e _ ν') (Finset.mem_univ ν.1)
    unfold softTerm at this
    rw [if_pos ν.2] at this
    exact this
  have hlog := Real.log_le_log (Real.exp_pos _) hterm
  rw [Real.log_exp] at hlog
  rw [softLen_eq]
  have h1 := mul_le_mul_of_nonneg_left hlog hs.le
  have h2 : softTemp q F j e * (-faceLen Δ j ν (sb j p) / softTemp q F j e) =
      -faceLen Δ j ν (sb j p) := by
    field_simp
  linarith

/-- `L − ζ/2 ≤ ℓ` (soft-min defect). -/
theorem softLen_ge (hΔ : Δ.Spec) (he : 0 < e) (p : Moments m) :
    Δ.sliceLen j p - zeta F j e / 2 ≤ softLen Δ F j e (sb j p) := by
  have hs := softTemp_pos (q := q) F j he
  have hz := zeta_pos F j he
  obtain ⟨ν0, hν0⟩ := hΔ.bounded_dir j
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (Fin.pos ν0)
  have hpos : 0 < ∑ ν, softTerm Δ F j e (sb j p) ν := by
    have := Finset.single_le_sum (f := softTerm Δ F j e (sb j p))
      (fun ν' _ => softTerm_nonneg Δ F j e _ ν') (Finset.mem_univ ν0)
    have h0 : 0 < softTerm Δ F j e (sb j p) ν0 := by
      unfold softTerm; rw [if_pos hν0]; positivity
    linarith
  have hle : ∑ ν, softTerm Δ F j e (sb j p) ν ≤
      q * Real.exp (-Δ.sliceLen j p / softTemp q F j e) := by
    calc ∑ ν, softTerm Δ F j e (sb j p) ν
        ≤ ∑ _ν : Fin q, Real.exp (-Δ.sliceLen j p / softTemp q F j e) := by
          refine Finset.sum_le_sum fun ν _ => ?_
          unfold softTerm
          split_ifs with h
          · apply Real.exp_le_exp.mpr
            apply div_le_div_of_nonneg_right _ hs.le
            linarith [sliceLen_le_faceLen Δ j p h]
          · positivity
      _ = q * Real.exp (-Δ.sliceLen j p / softTemp q F j e) := by simp
  have hlog : Real.log (∑ ν, softTerm Δ F j e (sb j p) ν) ≤
      Real.log q + -Δ.sliceLen j p / softTemp q F j e := by
    calc _ ≤ Real.log (q * Real.exp (-Δ.sliceLen j p / softTemp q F j e)) :=
          Real.log_le_log hpos hle
      _ = _ := by rw [Real.log_mul hq.ne' (Real.exp_pos _).ne', Real.log_exp]
  have h1 := mul_le_mul_of_nonneg_left hlog hs.le
  have h2 : softTemp q F j e * (-Δ.sliceLen j p / softTemp q F j e) = -Δ.sliceLen j p := by
    field_simp
  rw [mul_add, h2] at h1
  have h3 : softTemp q F j e * ((q : ℝ) + 1) = zeta F j e / 4 := by
    unfold softTemp
    have : (q : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  have h4 := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hq) hs.le
  have h5 : softShift F j e = zeta F j e / 4 := rfl
  rw [softLen_eq, h5]
  nlinarith

/-- Coordinates of points of `Δ` are below `boxRad − 2`. -/
theorem le_boxRad (hΔ : Δ.Spec) {p : Moments m} (hp : p ∈ Δ.set) (i : Fin m) :
    p i ≤ boxRad Δ - 2 := by
  obtain ⟨ν, hν⟩ := hΔ.bounded_dir i
  have hterm : ∀ (i' : Fin m) (ν' : Fin q),
      0 ≤ (if 0 < Δ.b ν' i' then Δ.ℓ ν' / Δ.b ν' i' else 0) := fun i' ν' => by
    split_ifs with h
    · exact div_nonneg (hΔ.ℓ_pos ν').le h.le
    · exact le_rfl
  have h1 : p i ≤ Δ.ℓ ν / Δ.b ν i := by
    rw [le_div_iff₀ hν]
    have h2 := hp.2 ν
    have h3 : Δ.b ν i * p i ≤ ∑ k, Δ.b ν k * p k :=
      Finset.single_le_sum (f := fun k => Δ.b ν k * p k)
        (fun k _ => mul_nonneg (hΔ.b_nonneg ν k) (hp.1 k)) (Finset.mem_univ i)
    linarith
  have h4 : Δ.ℓ ν / Δ.b ν i ≤ ∑ ν', (if 0 < Δ.b ν' i then Δ.ℓ ν' / Δ.b ν' i else 0) := by
    have := Finset.single_le_sum (f := fun ν' => if 0 < Δ.b ν' i then Δ.ℓ ν' / Δ.b ν' i else 0)
      (fun ν' _ => hterm i ν') (Finset.mem_univ ν)
    simp only [if_pos hν] at this
    exact this
  have h5 : ∑ ν', (if 0 < Δ.b ν' i then Δ.ℓ ν' / Δ.b ν' i else 0) ≤
      ∑ i', ∑ ν', (if 0 < Δ.b ν' i' then Δ.ℓ ν' / Δ.b ν' i' else 0) :=
    Finset.single_le_sum (f := fun i' => ∑ ν', (if 0 < Δ.b ν' i' then Δ.ℓ ν' / Δ.b ν' i' else 0))
      (fun i' _ => Finset.sum_nonneg fun ν' _ => hterm i' ν') (Finset.mem_univ i)
  unfold boxRad
  linarith

/-- On long slices of `Δ` the cutoff is `1`. -/
theorem cut_eq_one (hΔ : Δ.Spec) (he : 0 < e) {p : Moments m} (hp : p ∈ Δ.set)
    (hL : 2 * eta0 F j e ≤ Δ.sliceLen j p) : cut Δ F j e (sb j p) = 1 := by
  have hη := eta0_pos F j he
  have hR : 2 ≤ boxRad Δ := by linarith [le_boxRad hΔ hp j, hp.1 j]
  have hb : boxCut Δ j (sb j p) = 1 := by
    unfold boxCut
    refine Finset.prod_eq_one fun i _ => ?_
    by_cases h : i = j
    · rw [if_pos h]
    · rw [if_neg h, sb_ne h, Real.smoothTransition.zero_of_nonpos, sub_zero]
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      have h1 := le_boxRad hΔ hp i
      have h0 := hp.1 i
      nlinarith
  have hl : lenCut Δ F j e (sb j p) = 1 := by
    unfold lenCut
    refine Finset.prod_eq_one fun ν _ => ?_
    split_ifs with h
    · apply Real.smoothTransition.one_of_one_le
      have h1 := sliceLen_le_faceLen Δ j p h
      rw [le_div_iff₀ (by positivity)]
      linarith
    · rfl
  rw [cut, hb, hl, one_mul]

/-- Long slices of `Δ` lie in the planar parameter compact. -/
theorem mem_bigParams (hΔ : Δ.Spec) (he : 0 < e) {p : Moments m} (hp : p ∈ Δ.set)
    (hL : 2 * eta0 F j e ≤ Δ.sliceLen j p) : sb j p ∈ bigParams Δ F j e := by
  have hη := eta0_pos F j he
  have hR : 2 ≤ boxRad Δ := by linarith [le_boxRad hΔ hp j, hp.1 j]
  refine ⟨sb_self j p, fun i => ?_, fun ν hν => ?_⟩
  · by_cases h : i = j
    · rw [h, sb_self, abs_zero]; linarith
    · rw [sb_ne h, abs_of_nonneg (hp.1 i)]
      linarith [le_boxRad hΔ hp i]
  · linarith [sliceLen_le_faceLen Δ j p hν]

theorem sliceFn_eq (p : Moments m) :
    sliceFn Δ F j e (sb j p) =
      fun v => PolyFn.eval F (Function.update p j (softLen Δ F j e (sb j p) * v)) := by
  funext v
  unfold sliceFn
  rw [update_sb]

/-! ### Estimates along a slice -/

theorem coef_le_slope (F : PolyFn m) (j : Fin m) {a : AffinePiece m} (ha : a ∈ F) :
    |a.coef j| ≤ slopeBound F j := by
  unfold slopeBound
  have : |a.coef j| ≤ (F.map fun a => |a.coef j|).sum :=
    List.single_le_sum (fun x hx => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _) _
      (List.mem_map.mpr ⟨a, ha, rfl⟩)
  linarith

/-- `F` is `Λ`-Lipschitz along the slice. -/
theorem eval_update_le (hF : F ≠ []) (j : Fin m) (p : Moments m) (a b : ℝ) :
    PolyFn.eval F (Function.update p j a) ≤
      PolyFn.eval F (Function.update p j b) + slopeBound F j * |a - b| := by
  obtain ⟨r, hr, hra⟩ := PolyFn.eval_mem hF (Function.update p j a)
  rw [hra]
  have h1 := PolyFn.le_eval hr (Function.update p j b)
  rw [AffinePiece.eval_update] at h1 ⊢
  have h2 := coef_le_slope F j hr
  have h3 : r.coef j * (a - b) ≤ |r.coef j| * |a - b| := by
    rw [← abs_mul]; exact le_abs_self _
  have h4 : |r.coef j| * |a - b| ≤ slopeBound F j * |a - b| :=
    mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  nlinarith

theorem le_rearr (hΔ : Δ.Spec) {p : Moments m} (hp : p ∈ Δ.set) (j : Fin m)
    {G : Moments m → ℝ} {T : ℝ}
    (h : ∀ a : ℝ, 0 ≤ a → a ≤ Δ.sliceLen j p - p j →
      T ≤ max (G (Function.update p j a)) (G (Function.update p j (a + p j)))) :
    T ≤ rearr Δ j G p := by
  haveI := rearr_nonempty hΔ hp j
  unfold rearr
  exact le_ciInf fun a => h a a.2.1 a.2.2

theorem unitRearr_le {f : ℝ → ℝ} (hf : Continuous f) {x a : ℝ} (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1 - x) : unitRearr f x ≤ max (f a) (f (a + x)) := by
  have hbdd : BddBelow (Set.range fun b : Icc (0 : ℝ) (1 - x) => max (f b) (f (b + x))) := by
    have hc : Continuous fun b => max (f b) (f (b + x)) :=
      hf.max (hf.comp (continuous_id.add continuous_const))
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 - x)).bddBelow_image hc.continuousOn
    exact ⟨M, by rintro _ ⟨b, rfl⟩; exact hM ⟨b, b.2, rfl⟩⟩
  exact ciInf_le hbdd ⟨a, ha0, ha1⟩

/-- Short slices: everything moves inside `[0, L]`. -/
theorem core_short (hΔ : Δ.Spec) (hF : F ≠ []) {p : Moments m} (hp : p ∈ Δ.set) {x' E : ℝ}
    (hx0 : 0 ≤ x') (hxL : x' ≤ Δ.sliceLen j p) (hLe : slopeBound F j * Δ.sliceLen j p ≤ E) :
    PolyFn.eval F (Function.update p j x') ≤ rearr Δ j (PolyFn.eval F) p + E := by
  have hΛ := slopeBound_pos F j
  have hpj : 0 ≤ p j := hp.1 j
  have key := le_rearr hΔ hp j (G := PolyFn.eval F)
    (T := PolyFn.eval F (Function.update p j x') - slopeBound F j * Δ.sliceLen j p)
    fun a ha0 haL => by
      have h1 := eval_update_le hF j p x' a
      have h2 : |x' - a| ≤ Δ.sliceLen j p := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
      have h3 := mul_le_mul_of_nonneg_left h2 hΛ.le
      have h4 := le_max_left (PolyFn.eval F (Function.update p j a))
        (PolyFn.eval F (Function.update p j (a + p j)))
      linarith
  linarith

/-- Long slices, `x > ℓ`: the point is fixed. -/
theorem core_fixed (hΔ : Δ.Spec) (hF : F ≠ []) {p : Moments m} (hp : p ∈ Δ.set) {ℓ d : ℝ}
    (hℓ : ℓ < p j) (hd : Δ.sliceLen j p - ℓ ≤ d) :
    PolyFn.eval F (Function.update p j (p j)) ≤
      rearr Δ j (PolyFn.eval F) p + slopeBound F j * d := by
  have hΛ := slopeBound_pos F j
  have key := le_rearr hΔ hp j (G := PolyFn.eval F)
    (T := PolyFn.eval F (Function.update p j (p j)) - slopeBound F j * d)
    fun a ha0 haL => by
      have h1 := eval_update_le hF j p (p j) (a + p j)
      have h2 : |p j - (a + p j)| ≤ d := by
        rw [abs_sub_comm, show a + p j - p j = a by ring, abs_of_nonneg ha0]; linarith
      have h3 := mul_le_mul_of_nonneg_left h2 hΛ.le
      have h4 := le_max_right (PolyFn.eval F (Function.update p j a))
        (PolyFn.eval F (Function.update p j (a + p j)))
      linarith
  linarith

/-- Long slices, `x ≤ ℓ`: the rearrangement on the shortened slice `[0, ℓ]`. -/
theorem core_long (hΔ : Δ.Spec) (hF : F ≠ []) {p : Moments m} (hp : p ∈ Δ.set) {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hxl : p j ≤ ℓ) (hd0 : 0 ≤ d) (hd : Δ.sliceLen j p - ℓ ≤ d) :
    unitRearr (fun v => PolyFn.eval F (Function.update p j (ℓ * v))) (p j / ℓ) ≤
      rearr Δ j (PolyFn.eval F) p + slopeBound F j * d := by
  have hΛ := slopeBound_pos F j
  have hℓ0 : ℓ ≠ 0 := hℓ.ne'
  have hfc : Continuous fun v => PolyFn.eval F (Function.update p j (ℓ * v)) :=
    (PolyFn.eval_continuous F).comp
      (continuous_const.update j (continuous_const.mul continuous_id))
  have key := le_rearr hΔ hp j (G := PolyFn.eval F)
    (T := unitRearr (fun v => PolyFn.eval F (Function.update p j (ℓ * v))) (p j / ℓ) -
      slopeBound F j * d)
    fun a ha0 haL => by
      obtain ⟨a', ha'0, ha'1, ha'2, ha'3⟩ :
          ∃ a', 0 ≤ a' ∧ a' ≤ ℓ - p j ∧ a - a' ≤ d ∧ a' ≤ a := by
        by_cases hc : a ≤ ℓ - p j
        · exact ⟨a, ha0, hc, by linarith, le_rfl⟩
        · exact ⟨ℓ - p j, by linarith, le_rfl, by linarith, by linarith⟩
      have hU := unitRearr_le hfc (x := p j / ℓ) (a := a' / ℓ) (div_nonneg ha'0 hℓ.le) (by
        have : 1 - p j / ℓ = (ℓ - p j) / ℓ := by field_simp
        rw [this]; exact div_le_div_of_nonneg_right ha'1 hℓ.le)
      have e1 : ℓ * (a' / ℓ) = a' := by field_simp
      have e1' : ℓ * (p j / ℓ) = p j := by field_simp
      have e2 : ℓ * (a' / ℓ + p j / ℓ) = a' + p j := by rw [mul_add, e1, e1']
      simp only [e1, e2] at hU
      have h1 := eval_update_le hF j p a' a
      have h2 := eval_update_le hF j p (a' + p j) (a + p j)
      have k1 : |a' - a| ≤ d := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
      have k2 : |a' + p j - (a + p j)| ≤ d := abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
      have k3 := mul_le_mul_of_nonneg_left k1 hΛ.le
      have k4 := mul_le_mul_of_nonneg_left k2 hΛ.le
      have m1 := le_max_left (PolyFn.eval F (Function.update p j a))
        (PolyFn.eval F (Function.update p j (a + p j)))
      have m2 := le_max_right (PolyFn.eval F (Function.update p j a))
        (PolyFn.eval F (Function.update p j (a + p j)))
      have hm : max (PolyFn.eval F (Function.update p j a'))
          (PolyFn.eval F (Function.update p j (a' + p j))) ≤
          max (PolyFn.eval F (Function.update p j a))
            (PolyFn.eval F (Function.update p j (a + p j))) + slopeBound F j * d :=
        max_le (by linarith) (by linarith)
      linarith
  linarith

/-! ### The estimate -/

attribute [local irreducible] planarGen in
/-- **S-thm:plc-lift (c)** with `liftFamily` unfolded: `resc (planarGen y) (cut y) (softLen y)`
is the slice family at `y = sliceBase j p`. -/
theorem liftFamily_estimate_aux (hΔ : Δ.Spec) (hF : F ≠ []) (he : 0 < e)
    {p : Moments m} (hp : p ∈ Δ.set) {u : ℝ × ℝ} (hu : radialArea u = p j) :
    PolyFn.eval F (Function.update p j (radialArea (Return.flow
      (pvf (resc (planarGen Δ F j e (sb j p)) (cut Δ F j e (sb j p))
        (softLen Δ F j e (sb j p)))) 1 u))) ≤
      rearr Δ j (PolyFn.eval F) p + e := by
  have hspec := planarGen_spec hΔ hF j he
  obtain ⟨rB, hrB1, hrB⟩ := hspec.support
  have hBy : ∀ s w, rB < radialArea w → planarGen Δ F j e (sb j p) s w = 0 :=
    fun s w h => hrB _ s w h
  have hBs : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => planarGen Δ F j e (sb j p) x.1 x.2) :=
    hspec.smooth.comp (contDiff_const.prodMk contDiff_id)
  have hx0 : 0 ≤ p j := hp.1 j
  have hxL : p j ≤ Δ.sliceLen j p := Polytope.le_sliceLen hΔ hp j
  have hΛ := slopeBound_pos F j
  have hΛη : slopeBound F j * eta0 F j e = e / 64 := by
    unfold eta0
    have := hΛ.ne'
    field_simp
  have hη := eta0_pos F j he
  have hζ : zeta F j e = eta0 F j e / 8 := rfl
  have hℓlo := softLen_ge (F := F) (j := j) hΔ he p
  have hℓhi := softLen_le (F := F) (j := j) hΔ he p
  rcases lt_or_ge (Δ.sliceLen j p) (2 * eta0 F j e) with hL2 | hL2
  · -- short slice: the trivial bound
    refine core_short hΔ hF hp (radialArea_nonneg' _) ?_ ?_
    · by_cases hℓ : 0 < softLen Δ F j e (sb j p)
      · refine flow_disc (resc_smooth hBs _ _) (resc_radial hBy _ hℓ) (resc_time _ _) ?_ 1
          (by rw [hu]; exact hxL)
        nlinarith
      · rw [flow_resc_nonpos _ _ (not_lt.mp hℓ), hu]; exact hxL
    · nlinarith
  · -- long slice: `χ = 1`, rescaled planar estimate
    have hℓ : 0 < softLen Δ F j e (sb j p) := by linarith
    have hc := cut_eq_one (F := F) hΔ he hp hL2
    rw [hc]
    have hsq : Real.sqrt (softLen Δ F j e (sb j p)) ≠ 0 := (Real.sqrt_pos.mpr hℓ).ne'
    obtain ⟨w, rfl⟩ : ∃ w, u = Real.sqrt (softLen Δ F j e (sb j p)) • w :=
      ⟨_, (smul_inv_smul₀ hsq u).symm⟩
    rw [flow_resc hBs hBy 1 hℓ 1, Real.smoothTransition.one_of_one_le le_rfl, one_mul,
      radialArea_smul, Real.sq_sqrt hℓ.le]
    rw [radialArea_smul, Real.sq_sqrt hℓ.le] at hu
    have hd : slopeBound F j * (zeta F j e / 2) = e / 1024 := by rw [hζ]; linarith
    rcases le_or_gt (p j) (softLen Δ F j e (sb j p)) with hxl | hxl
    · have hw1 : radialArea w ≤ 1 := by
        by_contra h
        push_neg at h
        have := mul_lt_mul_of_pos_left h hℓ
        linarith
      have hww : radialArea w = p j / softLen Δ F j e (sb j p) :=
        eq_div_of_mul_eq hℓ.ne' (by rw [mul_comm]; exact hu)
      have hmem := mem_bigParams (F := F) hΔ he hp hL2
      have hest : sliceFn Δ F j e (sb j p)
            (radialArea (Return.flow (pvf (planarGen Δ F j e (sb j p))) 1 w)) ≤
          unitRearr (sliceFn Δ F j e (sb j p)) (radialArea w) + planarTol e :=
        hspec.estimate _ hmem w hw1
      rw [sliceFn_eq, hww] at hest
      have hcore := core_long hΔ hF hp hℓ hxl (d := zeta F j e / 2) (by linarith) (by linarith)
      have ht : planarTol e = e / 4 := rfl
      simp only at hest
      linarith
    · have hrw : rB < radialArea w := by
        by_contra h
        push_neg at h
        have h1 : radialArea w ≤ 1 := h.trans hrB1.le
        have := mul_le_mul_of_nonneg_left h1 hℓ.le
        linarith
      rw [flow_fix hBs hBy hrw 1, hu]
      have hcore := core_fixed hΔ hF hp hxl (d := zeta F j e / 2) (by linarith)
      linarith

end slice

end SymplecticPacking.HighDim.LiftEst
