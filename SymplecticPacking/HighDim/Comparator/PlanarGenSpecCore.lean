import SymplecticPacking.HighDim.Comparator.PlanarGen
import SymplecticPacking.Return.Flow

/-!
# Generic reductions for `RealiseGen.planarGen_spec`

Lemmas about the explicit planar generator `PlanarGen.Input.gen` that reduce the
planar contract `PlanarSpec` to three statements about the five-segment path data
`Input.pathData y` (ordinariness, joint smoothness in the parameter, endpoint estimate):

* `paramCut_eq_one`: the parameter cutoff is `1` on the parameter compact;
* `gen_support`: if every `pathData y` with `ψ(y) ≠ 0` is an ordinary path, the generator has
  common spatial support in the disc of capacity `P_supp < 1`;
* `flow_Qham`: for an ordinary path `P`, the time-one map of the planar field of
  `(s, w) ↦ Q_s(w₁ + i w₂)` (convention `ι_X ω = −dQ`) is `q̂_1` (in real coordinates).
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen

open Set Complex Filter Topology
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff Real

variable {m q : ℕ}

/-! ### Real coordinates of the plane -/

/-- `ℝ × ℝ → ℂ`, `(a, b) ↦ a + ib`, as a continuous linear map. -/
def cplx : ℝ × ℝ →L[ℝ] ℂ := Complex.equivRealProdCLM.symm.toContinuousLinearMap

theorem cplx_apply (v : ℝ × ℝ) : cplx v = (⟨v.1, v.2⟩ : ℂ) := by
  apply Complex.ext <;> simp [cplx, Complex.equivRealProdCLM_symm_apply]

theorem cplx_01 : cplx (0, 1) = I := by rw [cplx_apply]; apply Complex.ext <;> simp

theorem cplx_10 : cplx (1, 0) = 1 := by rw [cplx_apply]; apply Complex.ext <;> simp

theorem area_mk (w : ℝ × ℝ) : π * ‖(⟨w.1, w.2⟩ : ℂ)‖ ^ 2 = π * (w.1 ^ 2 + w.2 ^ 2) := by
  rw [Complex.sq_norm, Complex.normSq_mk]; ring

theorem norm_le_norm_mk (v : ℝ × ℝ) : ‖v‖ ≤ ‖(⟨v.1, v.2⟩ : ℂ)‖ := by
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · rw [Real.norm_eq_abs]
    exact Complex.abs_re_le_norm (⟨v.1, v.2⟩ : ℂ)
  · rw [Real.norm_eq_abs]
    exact Complex.abs_im_le_norm (⟨v.1, v.2⟩ : ℂ)

/-- Points of sup-norm `> √(|P|/π) + 1` have capacity `> P`. -/
theorem lt_area_of_norm {P : ℝ} {v : ℝ × ℝ} (hv : √(|P| / π) + 1 < ‖v‖) :
    P < π * ‖(⟨v.1, v.2⟩ : ℂ)‖ ^ 2 := by
  have h1 : √(|P| / π) < ‖(⟨v.1, v.2⟩ : ℂ)‖ := by linarith [norm_le_norm_mk v]
  have h2 : |P| / π < ‖(⟨v.1, v.2⟩ : ℂ)‖ ^ 2 := Real.lt_sq_of_sqrt_lt h1
  have h3 : |P| < π * ‖(⟨v.1, v.2⟩ : ℂ)‖ ^ 2 := by
    rwa [div_lt_iff₀ Real.pi_pos, mul_comm] at h2
  linarith [le_abs_self P]

/-! ### The parameter cutoff -/

/-- `ψ = 1` on `{‖y‖_∞ ≤ 3R, all L_ν(y) ≥ 3η₀/4}`. -/
theorem paramCut_eq_one {Δ : Polytope m q} {j : Fin m} {Lν : Fin q → Moments m → ℝ}
    {R η₀ : ℝ} {y : Moments m} (hR : 0 < R) (hη : 0 < η₀) (hy : ∀ i, |y i| ≤ 3 * R)
    (hL : ∀ ν, 0 < Δ.b ν j → 3 * η₀ / 4 ≤ Lν ν y) : paramCut Δ j Lν R η₀ y = 1 := by
  have h1 : ∀ i, Real.smoothTransition ((16 * R ^ 2 - y i ^ 2) / (7 * R ^ 2)) = 1 := by
    intro i
    apply Real.smoothTransition.one_of_one_le
    rw [le_div_iff₀ (by positivity)]
    have ha := hy i
    have hb : y i ^ 2 ≤ 9 * R ^ 2 := by
      have := sq_abs (y i)
      nlinarith [abs_nonneg (y i)]
    nlinarith
  have h2 : ∀ ν, (if 0 < Δ.b ν j then
      Real.smoothTransition ((Lν ν y - η₀ / 2) / (η₀ / 4)) else 1) = 1 := by
    intro ν
    split_ifs with h
    · apply Real.smoothTransition.one_of_one_le
      rw [le_div_iff₀ (by positivity)]
      linarith [hL ν h]
    · rfl
  simp only [paramCut, h1, h2, Finset.prod_const_one, one_mul]

/-! ### Common support -/

namespace Input

variable (D : Input m)

/-- If every path `pathData y` with `ψ(y) ≠ 0` is ordinary, the generator vanishes outside the
disc of capacity `P_supp`, and `P_supp < 1`. -/
theorem gen_support (hO : ∀ y, D.cutoff y ≠ 0 → Qhat.OrdinaryPath (D.pathData y)) :
    ∃ rB < 1, ∀ y s (w : ℝ × ℝ), rB < π * (w.1 ^ 2 + w.2 ^ 2) → D.gen y s w = 0 := by
  by_cases hex : ∃ y, D.cutoff y ≠ 0
  · obtain ⟨y₀, hy₀⟩ := hex
    have hlt : D.Psupp < 1 := (hO y₀ hy₀).Psupp_lt_h
    refine ⟨D.Psupp, hlt, fun y s w hw => ?_⟩
    by_cases hy : D.cutoff y = 0
    · exact gen_of_cutoff_eq_zero hy s w
    · unfold gen rawGen
      have hw' : (D.pathData y).Psupp < π * ‖(⟨w.1, w.2⟩ : ℂ)‖ ^ 2 := by
        rw [area_mk]; exact hw
      rw [Qhat.Qham_support (hO y hy) hw', mul_zero]
  · push_neg at hex
    exact ⟨0, one_pos, fun y s w _ => gen_of_cutoff_eq_zero (hex y) s w⟩

end Input

/-! ### The flow of the planar field of `Q` -/

section flow

variable {P : Qhat.PathData} (hP : Qhat.OrdinaryPath P)
include hP

/-- The planar field of `(s, u) ↦ Q_s(u₁ + i u₂)`, convention `ι_X ω = −dQ`. -/
def qField (P : Qhat.PathData) (s : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (-(fderiv ℝ (fun u : ℝ × ℝ => Qhat.Qham P s ⟨u.1, u.2⟩) v (0, 1)),
    fderiv ℝ (fun u : ℝ × ℝ => Qhat.Qham P s ⟨u.1, u.2⟩) v (1, 0))

theorem Qham_differentiableAt (s : ℝ) (z : ℂ) : DifferentiableAt ℝ (Qhat.Qham P s) z :=
  (((Qhat.Qham_smooth hP).comp (contDiff_const.prodMk contDiff_id)).differentiable
    (by simp) z)

theorem fderiv_Qham_mk (s : ℝ) (v : ℝ × ℝ) :
    fderiv ℝ (fun u : ℝ × ℝ => Qhat.Qham P s ⟨u.1, u.2⟩) v =
      (fderiv ℝ (Qhat.Qham P s) (cplx v)).comp cplx := by
  have hG : (fun u : ℝ × ℝ => Qhat.Qham P s ⟨u.1, u.2⟩) = Qhat.Qham P s ∘ cplx :=
    funext fun u => by simp [cplx_apply]
  rw [hG, fderiv_comp _ (Qham_differentiableAt hP s _) cplx.differentiableAt,
    ContinuousLinearMap.fderiv]

theorem qField_eq (s : ℝ) (v : ℝ × ℝ) :
    qField P s v = (-(fderiv ℝ (Qhat.Qham P s) (cplx v) I), fderiv ℝ (Qhat.Qham P s) (cplx v) 1) := by
  simp only [qField, fderiv_Qham_mk hP, ContinuousLinearMap.coe_comp', Function.comp_apply,
    cplx_01, cplx_10]

theorem qField_csField : Return.CSField (qField P) := by
  have hf : ContDiff ℝ ∞
      (Function.uncurry fun (p : ℝ × (ℝ × ℝ)) (v : ℝ × ℝ) => Qhat.Qham P p.1 ⟨v.1, v.2⟩) := by
    have he : (Function.uncurry fun (p : ℝ × (ℝ × ℝ)) (v : ℝ × ℝ) => Qhat.Qham P p.1 ⟨v.1, v.2⟩) =
        (fun p : ℝ × ℂ => Qhat.Qham P p.1 p.2) ∘ fun x : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
          (x.1.1, cplx x.2) := by
      funext x; simp [Function.uncurry, cplx_apply]
    rw [he]
    exact (Qhat.Qham_smooth hP).comp
      ((contDiff_fst.comp contDiff_fst).prodMk (cplx.contDiff.comp contDiff_snd))
  have hD : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) =>
      fderiv ℝ (fun u : ℝ × ℝ => Qhat.Qham P p.1 ⟨u.1, u.2⟩) p.2) :=
    ContDiff.fderiv (f := fun (p : ℝ × (ℝ × ℝ)) (v : ℝ × ℝ) => Qhat.Qham P p.1 ⟨v.1, v.2⟩) hf
      contDiff_snd (le_of_eq rfl)
  refine ⟨?_, ?_⟩
  · show ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) =>
      ((-(fderiv ℝ (fun u : ℝ × ℝ => Qhat.Qham P p.1 ⟨u.1, u.2⟩) p.2 (0, 1)),
        fderiv ℝ (fun u : ℝ × ℝ => Qhat.Qham P p.1 ⟨u.1, u.2⟩) p.2 (1, 0)) : ℝ × ℝ))
    exact (hD.clm_apply contDiff_const).neg.prodMk (hD.clm_apply contDiff_const)
  · set R : ℝ := √(|P.Psupp| / π) + 1
    refine HasCompactSupport.intro
      (K := Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : ℝ × ℝ) R)
      (isCompact_Icc.prod (isCompact_closedBall 0 R)) ?_
    rintro ⟨t, u⟩ hp
    simp only [mem_prod, Metric.mem_closedBall, dist_zero_right, not_and_or, not_le] at hp
    have h0 : fderiv ℝ (fun u : ℝ × ℝ => Qhat.Qham P t ⟨u.1, u.2⟩) u = 0 := by
      rcases hp with ht | hu
      · have ht' : t ≤ 0 ∨ 1 ≤ t := by
          rcases not_and_or.mp ht with h | h
          · exact Or.inl (not_le.mp h).le
          · exact Or.inr (not_le.mp h).le
        have : (fun u : ℝ × ℝ => Qhat.Qham P t ⟨u.1, u.2⟩) = fun _ => 0 :=
          funext fun v => Qhat.Qham_time hP ht' _
        rw [this]; simp
      · have : (fun u : ℝ × ℝ => Qhat.Qham P t ⟨u.1, u.2⟩) =ᶠ[𝓝 u] fun _ => 0 := by
          filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hu] with v hv
          exact Qhat.Qham_support hP (lt_area_of_norm hv)
        rw [this.fderiv_eq]; simp
    show qField P t u = 0
    simp [qField, h0]

/-- **The time-one map of `qField P` is `q̂_1`** (in real coordinates). -/
theorem flow_qField (w : ℝ × ℝ) :
    Return.flow (qField P) 1 w =
      ((Qhat.qhat P 1 ⟨w.1, w.2⟩).re, (Qhat.qhat P 1 ⟨w.1, w.2⟩).im) := by
  have hV := qField_csField hP
  set z : ℂ := ⟨w.1, w.2⟩
  set u : ℝ → ℝ × ℝ := fun s => ((Qhat.qhat P s z).re, (Qhat.qhat P s z).im) with hu
  have hsol : Return.IsSolFrom (qField P) 0 w u := by
    refine ⟨?_, fun s => ?_⟩
    · simp [hu, Qhat.qhat_zero hP, z]
    · have h := Qhat.qhat_hamiltonian hP s z
      have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s h
      have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s h
      have hprod := hre.prodMk him
      have hc : cplx (u s) = Qhat.qhat P s z := by
        rw [cplx_apply]
      have hv : qField P s (u s) =
          ((Qhat.hamVF2 (Qhat.Qham P s) (Qhat.qhat P s z)).re,
            (Qhat.hamVF2 (Qhat.Qham P s) (Qhat.qhat P s z)).im) := by
        rw [qField_eq hP, hc]
        simp [Qhat.hamVF2]
      rw [hv]
      show HasDerivAt (fun s => ((Qhat.qhat P s z).re, (Qhat.qhat P s z).im)) _ s
      simpa [Function.comp_def] using hprod
  rw [Return.flow, hV.flowFrom_eq hsol 1]

end flow

end SymplecticPacking.HighDim.PlanarGen
