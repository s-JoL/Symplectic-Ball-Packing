import SymplecticPacking.HighDim.Comparator.PlanarDensityBounds
import SymplecticPacking.HighDim.Comparator.PlanarAreaGate

/-!
# Normalization of the finite-area planar density

A constant-tail auxiliary density supplies a globally proper inverse. Locality
then identifies it with the original formulas on the source disc.
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen

open Set Filter Topology Complex
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff Real

/-- The cancellation of Jacobians only uses the target Jacobian at the preimage. -/
lemma normalize_det_at {J : ℝ → ℂ → ℝ} {s₁ s₂ j ρ s : ℝ}
    (hJ : Inner.FlatDensity J s₁ s₂ j ρ) (hs : s ∈ Ioo s₁ s₂)
    {G : ℂ → ℂ} (hG : Differentiable ℝ G) (z : ℂ)
    (hGdet : LinearMap.det (fderiv ℝ G (Inner.TrotInv J s (Inner.Darea J s z)) : ℂ →ₗ[ℝ] ℂ) =
      J s (Inner.TrotInv J s (Inner.Darea J s z))) :
    LinearMap.det (fderiv ℝ (fun z => G (Inner.TrotInv J s (Inner.Darea J s z))) z : ℂ →ₗ[ℝ] ℂ) = 1 := by
  have hTi := (Inner.TrotInv_smooth_of_const hJ hs).differentiable (by simp)
  have hD := (Inner.Darea_smooth_of_const hJ hs).differentiable (by simp)
  have hc : (fun z => G (Inner.TrotInv J s (Inner.Darea J s z))) = G ∘ (Inner.TrotInv J s ∘ Inner.Darea J s) := rfl
  rw [hc, fderiv_comp z (hG _) ((hTi _).comp z (hD z)), fderiv_comp z (hTi _) (hD z),
    ContinuousLinearMap.toLinearMap_comp, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
    LinearMap.det_comp]
  simp only [Function.comp_apply]
  set v := Inner.Darea J s z
  set w := Inner.TrotInv J s v
  have h1 := Inner.det_TrotInv_mul hJ hs v
  have h2 := Inner.Darea_pullback hJ hs z
  rw [Inner.Trot_det hJ.smooth (hJ.pos s hs)] at h1
  have hnw : ‖w‖ = ‖v‖ := Inner.norm_TrotInv hJ hs v
  rw [hnw] at h1
  rw [hGdet]
  have hJw := (hJ.pos s hs w).ne'
  have hJb := (Inner.Jbar_pos hJ.cont (hJ.pos s hs) (‖v‖ ^ 2)).ne'
  set a := LinearMap.det (fderiv ℝ (Inner.TrotInv J s) v : ℂ →ₗ[ℝ] ℂ)
  set b := LinearMap.det (fderiv ℝ (Inner.Darea J s) z : ℂ →ₗ[ℝ] ℂ)
  have hh : J s w * (a * b) =
      (J s w / Inner.Jbar J s (‖v‖ ^ 2) * a) * (Inner.Jbar J s (‖v‖ ^ 2) * b) := by field_simp
  rw [hh, h1, h2, one_mul]

namespace Input

variable {m : ℕ} (D : PlanarGen.Input m) (y : Moments m)
variable (hξ : 0 < D.xi) (hL : 0 ≤ D.L) (hne : D.pieces y ≠ [])
    (hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L)
include hξ hL hne hb

lemma Xs_hasDerivAt (s u : ℝ) :
    HasDerivAt (D.Xs y s) ((1 - s) * D.a0 y + s * deriv (D.XU y) u) u := by
  convert (((hasDerivAt_id u).const_mul ((1 - s) * D.a0 y)).add
    (((D.XU_smooth y hξ hL hne hb).differentiable (by simp) u).hasDerivAt.const_mul s)) using 1 <;> first | rfl | simp

lemma Ys_hasDerivAt (s v : ℝ) :
    HasDerivAt (D.Ys s) ((1 - s) * D.b0 + s * deriv D.XV v) v := by
  convert (((hasDerivAt_id v).const_mul ((1 - s) * D.b0)).add
    (((D.XV_smooth y hξ hL hne hb).differentiable (by simp) v).hasDerivAt.const_mul s)) using 1 <;> first | rfl | simp

lemma Xs_smooth (s : ℝ) : ContDiff ℝ ∞ (D.Xs y s) :=
  (contDiff_const.mul contDiff_id).add (contDiff_const.mul (D.XU_smooth y hξ hL hne hb))

lemma Ys_smooth (s : ℝ) : ContDiff ℝ ∞ (D.Ys s) :=
  (contDiff_const.mul contDiff_id).add (contDiff_const.mul (D.XV_smooth y hξ hL hne hb))

lemma Fs_smooth : ContDiff ℝ ∞ (fun p : ℝ × ℂ => D.Fs y p.1 p.2) := by
  have hu : ContDiff ℝ ∞ (fun p : ℝ × ℂ => D.XU y p.2.re) :=
    (D.XU_smooth y hξ hL hne hb).comp (reCLM.contDiff.comp contDiff_snd)
  have hv : ContDiff ℝ ∞ (fun p : ℝ × ℂ => D.XV p.2.im) :=
    (D.XV_smooth y hξ hL hne hb).comp (imCLM.contDiff.comp contDiff_snd)
  have hx : ContDiff ℝ ∞ (fun p : ℝ × ℂ => D.Xs y p.1 p.2.re) :=
    (((contDiff_const.sub contDiff_fst).mul contDiff_const).mul (reCLM.contDiff.comp contDiff_snd)).add
      (contDiff_fst.mul hu)
  have hy : ContDiff ℝ ∞ (fun p : ℝ × ℂ => D.Ys p.1 p.2.im) :=
    (((contDiff_const.sub contDiff_fst).mul contDiff_const).mul (imCLM.contDiff.comp contDiff_snd)).add
      (contDiff_fst.mul hv)
  exact (ofRealCLM.contDiff.comp hx).add ((ofRealCLM.contDiff.comp hy).mul contDiff_const)

lemma Fs_det (s : ℝ) (w : ℂ) :
    LinearMap.det (fderiv ℝ (D.Fs y s) w : ℂ →ₗ[ℝ] ℂ) = D.Js y s w := by
  have hh := AreaGate.productMap_det (D.Xs_smooth y hξ hL hne hb s) (D.Ys_smooth y hξ hL hne hb s) w
  change LinearMap.det (fderiv ℝ (D.Fs y s) w : ℂ →ₗ[ℝ] ℂ) = _ at hh
  rw [(D.Xs_hasDerivAt y hξ hL hne hb s w.re).deriv,
    (D.Ys_hasDerivAt y hξ hL hne hb s w.im).deriv] at hh
  exact hh

lemma Fs_injective {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : Function.Injective (D.Fs y s) := by
  have convex (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < (1 - s) * a + s * b := by
    by_cases h0 : s = 0
    · simp [h0, ha]
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hs.2) ha.le)
        (mul_pos (lt_of_le_of_ne hs.1 (Ne.symm h0)) hb)
  apply AreaGate.productMap_injective
  · apply strictMono_of_hasDerivAt_pos (D.Xs_hasDerivAt y hξ hL hne hb s)
    exact fun u => convex _ _ (D.a0_pos_from_pieces y hξ hL hne hb) (D.XU_deriv_pos y hξ hL hne hb u)
  · apply strictMono_of_hasDerivAt_pos (D.Ys_hasDerivAt y hξ hL hne hb s)
    exact fun v => convex _ _ (D.b0_pos_of_pieces y hξ hL hne hb)
      (Branch2.Planar.Well.X_deriv_pos (D.wellV_hyp y hξ hL hne hb) v)

/-- At time zero the density is constant on the whole plane. -/
lemma Js_zero (w : ℂ) : D.Js y 0 w = D.a0 y * D.b0 := by simp [Js]

/-- The initial normalized map is exactly the prescribed diagonal linear map. -/
theorem fs_zero (z : ℂ) :
    D.fs y 0 z = ((D.cx y * z.re : ℝ) : ℂ) + ((D.cy y * z.im : ℝ) : ℂ) * I := by
  have hj : 0 < D.a0 y * D.b0 :=
    mul_pos (D.a0_pos_from_pieces y hξ hL hne hb) (D.b0_pos_of_pieces y hξ hL hne hb)
  unfold fs
  rw [DensityExtension.normalize_constant hj (D.Js_zero y hξ hL hne hb) z]
  simp only [Fs, Xs, Ys, sub_zero, one_mul, zero_mul, add_zero,
    Complex.div_ofReal_re, Complex.div_ofReal_im]
  unfold cx cy j0
  push_cast
  ring

variable (hbM : ∀ p ∈ D.pieces y, |p.1| + |p.2| ≤ D.M)
include hbM

lemma Ebar_pos_from_pieces : 0 < D.Ebar := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
  have hM : 0 ≤ D.M := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hbM p hp)
  have hrect := D.Erect_pos hξ hL hM
  have hK : 0 < D.Kmin := by
    unfold Kmin amin
    have ha := D.alphaMax_pos_of_pieces y hξ hL hne hb
    have hb0 := D.b0_pos_of_pieces y hξ hL hne hb
    positivity
  have hp0 := D.pdag_pos hξ hL
  have hA := D.Amin_gt_pdag hξ hL
  have hfrac : 0 < D.pdag * D.Amin / (D.Kmin * (D.Amin - D.pdag)) :=
    div_pos (mul_pos hp0 (hp0.trans hA)) (mul_pos hK (sub_pos.mpr hA))
  unfold Ebar
  linarith

/-- The inverse normalization has squared radius below the common energy level. -/
theorem normalizer_energy {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : Real.pi * ‖z‖ ^ 2 < D.pdag) :
    ‖Inner.TrotInv (D.Js y) s (Inner.Darea (D.Js y) s z)‖ ^ 2 < D.Ebar := by
  have hE := D.Ebar_pos_from_pieces y hξ hL hne hb hbM
  have hR := Real.sqrt_pos.mpr hE
  obtain ⟨δ, hδ, hK⟩ := D.densityExtension_hyp y hξ hL hne hb hR
  have hs' : s ∈ Ioo (-δ) (1 + δ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hgate : Real.pi * ‖z‖ ^ 2 < Inner.Acal (D.Js y) s (Real.sqrt D.Ebar ^ 2) := by
    rw [Real.sq_sqrt hE.le]
    exact hz.trans (D.Ebar_area_gate y hξ hL hne hb hbM hs)
  have hh := DensityExtension.normalize_local hK hs' hR.le
    (D.Js_slice_continuous y hξ hL hne hb s) (D.Js_pos y hξ hL hne hb hs)
    (fun w hw => (DensityExtension.extend_eq hR hw).symm) hgate
  rw [hh.1]
  have hsq := (sq_lt_sq₀ (norm_nonneg _) hR.le).mpr hh.2
  rwa [Real.sq_sqrt hE.le] at hsq

/-- Area of the normalizer preimage equals source capacity. -/
theorem normalizer_area {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : Real.pi * ‖z‖ ^ 2 < D.pdag) :
    Inner.Acal (D.Js y) s (‖Inner.TrotInv (D.Js y) s (Inner.Darea (D.Js y) s z)‖ ^ 2) = Real.pi * ‖z‖ ^ 2 := by
  have hE := D.Ebar_pos_from_pieces y hξ hL hne hb hbM
  have hR := Real.sqrt_pos.mpr hE
  obtain ⟨δ, hδ, hK⟩ := D.densityExtension_hyp y hξ hL hne hb hR
  have hs' : s ∈ Ioo (-δ) (1 + δ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  apply DensityExtension.normalize_acal hK hs' hR.le
    (D.Js_slice_continuous y hξ hL hne hb s) (D.Js_pos y hξ hL hne hb hs)
    (fun w hw => (DensityExtension.extend_eq hR hw).symm)
  rw [Real.sq_sqrt hE.le]
  exact hz.trans (D.Ebar_area_gate y hξ hL hne hb hbM hs)

/-- Joint smoothness in deformation time and source on the complete source disc. -/
theorem fs_smooth : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => D.fs y p.1 p.2)
    (Icc 0 1 ×ˢ {z : ℂ | Real.pi * ‖z‖ ^ 2 < D.pdag}) := by
  have hE := D.Ebar_pos_from_pieces y hξ hL hne hb hbM
  have hR := Real.sqrt_pos.mpr hE
  obtain ⟨δ, hδ, hK⟩ := D.densityExtension_hyp y hξ hL hne hb hR
  let K := DensityExtension.extend (D.Js y) (D.a0 y * D.b0) (Real.sqrt D.Ebar)
  have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => (p.1, Inner.Darea K p.1 p.2))
      (Ioo (-δ) (1 + δ) ×ˢ univ) := contDiffOn_fst.prodMk (Inner.Darea_param_smooth hK)
  have h2 : ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => (p.1, Inner.TrotInv K p.1 (Inner.Darea K p.1 p.2)))
      (Ioo (-δ) (1 + δ) ×ˢ univ) :=
    contDiffOn_fst.prodMk ((Inner.TrotInv_param_smooth hK).comp h1 (fun p hp => ⟨hp.1, mem_univ _⟩))
  have h3 := (D.Fs_smooth y hξ hL hne hb).contDiffOn.comp h2 (fun p hp => mem_univ _)
  have h4 := h3.mono (show Icc (0 : ℝ) 1 ×ˢ {z : ℂ | Real.pi * ‖z‖ ^ 2 < D.pdag} ⊆
      Ioo (-δ) (1 + δ) ×ˢ univ from fun p hp => ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩, mem_univ _⟩)
  apply h4.congr
  intro p hp
  unfold fs
  congr 1
  apply (DensityExtension.normalize_local hK
    (show p.1 ∈ Ioo (-δ) (1 + δ) from ⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩) hR.le
    (D.Js_slice_continuous y hξ hL hne hb p.1) (D.Js_pos y hξ hL hne hb hp.1)
    (fun w hw => (DensityExtension.extend_eq hR hw).symm) ?_).1
  rw [Real.sq_sqrt hE.le]
  exact hp.2.trans (D.Ebar_area_gate y hξ hL hne hb hbM hp.1)

/-- The normalization preserves area on its source disc. -/
theorem fs_det {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : Real.pi * ‖z‖ ^ 2 < D.pdag) :
    LinearMap.det (fderiv ℝ (D.fs y s) z : ℂ →ₗ[ℝ] ℂ) = 1 := by
  have hE := D.Ebar_pos_from_pieces y hξ hL hne hb hbM
  have hR := Real.sqrt_pos.mpr hE
  obtain ⟨δ, hδ, hK⟩ := D.densityExtension_hyp y hξ hL hne hb hR
  let K := DensityExtension.extend (D.Js y) (D.a0 y * D.b0) (Real.sqrt D.Ebar)
  have hs' : s ∈ Ioo (-δ) (1 + δ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hlocal {u : ℂ} (hu : Real.pi * ‖u‖ ^ 2 < D.pdag) :
      Inner.TrotInv (D.Js y) s (Inner.Darea (D.Js y) s u) = Inner.TrotInv K s (Inner.Darea K s u) ∧
      ‖Inner.TrotInv K s (Inner.Darea K s u)‖ < Real.sqrt D.Ebar := by
    apply DensityExtension.normalize_local hK hs' hR.le
      (D.Js_slice_continuous y hξ hL hne hb s) (D.Js_pos y hξ hL hne hb hs)
      (fun w hw => (DensityExtension.extend_eq hR hw).symm)
    rw [Real.sq_sqrt hE.le]
    exact hu.trans (D.Ebar_area_gate y hξ hL hne hb hbM hs)
  have heq : D.fs y s =ᶠ[𝓝 z] fun u => D.Fs y s (Inner.TrotInv K s (Inner.Darea K s u)) := by
    filter_upwards [(isOpen_lt (continuous_const.mul (continuous_norm.pow 2)) continuous_const).mem_nhds hz]
      with u hu
    exact congrArg (D.Fs y s) (hlocal hu).1
  rw [heq.fderiv_eq]
  apply normalize_det_at hK hs' ((AreaGate.productMap_smooth (D.Xs_smooth y hξ hL hne hb s) (D.Ys_smooth y hξ hL hne hb s)).differentiable (by simp)) z
  change LinearMap.det (fderiv ℝ (D.Fs y s) (Inner.TrotInv K s (Inner.Darea K s z)) : ℂ →ₗ[ℝ] ℂ) = _
  rw [D.Fs_det y hξ hL hne hb]
  exact (DensityExtension.extend_eq hR (hlocal hz).2.le).symm

/-- The normalization is injective on the entire source disc. -/
theorem fs_injOn {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    InjOn (D.fs y s) {z : ℂ | Real.pi * ‖z‖ ^ 2 < D.pdag} := by
  have hE := D.Ebar_pos_from_pieces y hξ hL hne hb hbM
  have hR := Real.sqrt_pos.mpr hE
  obtain ⟨δ, hδ, hK⟩ := D.densityExtension_hyp y hξ hL hne hb hR
  let K := DensityExtension.extend (D.Js y) (D.a0 y * D.b0) (Real.sqrt D.Ebar)
  have hs' : s ∈ Ioo (-δ) (1 + δ) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have heq {u : ℂ} (hu : Real.pi * ‖u‖ ^ 2 < D.pdag) :
      D.fs y s u = D.Fs y s (Inner.TrotInv K s (Inner.Darea K s u)) := by
    apply congrArg (D.Fs y s)
    apply (DensityExtension.normalize_local hK hs' hR.le
      (D.Js_slice_continuous y hξ hL hne hb s) (D.Js_pos y hξ hL hne hb hs)
      (fun w hw => (DensityExtension.extend_eq hR hw).symm) ?_).1
    rw [Real.sq_sqrt hE.le]
    exact hu.trans (D.Ebar_area_gate y hξ hL hne hb hbM hs)
  intro u hu v hv huv
  rw [heq hu, heq hv] at huv
  have hpre := D.Fs_injective y hξ hL hne hb hs huv
  have harea := congrArg (Inner.Trot K s) hpre
  rw [Inner.Trot_TrotInv hK hs', Inner.Trot_TrotInv hK hs'] at harea
  exact (Inner.Darea_bijective hK hs').1 harea

end Input
end SymplecticPacking.HighDim.PlanarGen
