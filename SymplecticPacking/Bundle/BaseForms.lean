import SymplecticPacking.Bundle.TorusCalculus
import SymplecticPacking.Bundle.SigmaPos
import SymplecticPacking.Bundle.BPoints

/-!
# The base forms on the universal cover

`sec:fer` (`lem:fer-sigma`, `def:fer-frame`, `lem:fer-frame`): the base
forms `η_H`, `σ`, `λ_C` on the universal cover, computed from the theta lift `Zunit`.

* `d_etaH`: `d(Zunit^* η_H) = σ` (symmetry of second derivatives of `Zunit`).
* `lambdaC = η_H − (1/2π) Im(dZ₀/Z₀)` (`lambdaCu`, `lambdaCv`); `d_lambdaC`: `dλ_C = σ` where
  `Z₀ ≠ 0`; `lambdaC_descends`: `λ_C` is `1`-periodic in `u` and `v` (the deck transformations
  multiply `Zunit` by unit phases, `Zunit_add_one_left`, `Zunit_add_one_right`).
* `integral_sigma`: `∫₀¹∫₀¹ σ = 3`, by Stokes on the unit square: the edges `u = 0, 1` cancel,
  and along `v = 0, 1` the lift differs by the phase `φ(u) = e(u)/|e(u)|`,
  `e(u) = θ-factor³ = −exp(−3πiτ − 6πiu)`, of winding number `−3`.
* `frameA`: the frame `(Z₀/|Z₀|)³` over `𝒜⁺`; `angularForm_frameA` (`lem:fer-frame`): the
  angular forms `a_𝒜 = −3λ_C` and `a_loc = −3η_H` differ by `d(arg frameA)/2π`.
-/

noncomputable section

namespace SymplecticPacking.Bundle

open _root_.Complex ComplexConjugate Set Filter Topology MeasureTheory
open scoped Real ContDiff

/-! ### Hermitian product -/

lemma herm3_self (Z : Fin 3 → ℂ) : herm3 Z Z = (normSq3 Z : ℂ) := by
  simp only [herm3, normSq3, Fin.sum_univ_three, ofReal_add, ofReal_pow]
  simp only [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ofReal_pow]

lemma herm3_swap (Z W : Fin 3 → ℂ) : herm3 W Z = conj (herm3 Z W) := by
  simp only [herm3, map_sum, map_mul, conj_conj]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma herm3_add_right (Z W W' : Fin 3 → ℂ) : herm3 Z (W + W') = herm3 Z W + herm3 Z W' := by
  simp only [herm3, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma herm3_smul_left (c : ℂ) (Z W : Fin 3 → ℂ) : herm3 (c • Z) W = conj c * herm3 Z W := by
  simp only [herm3, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma herm3_smul_right (c : ℂ) (Z W : Fin 3 → ℂ) : herm3 Z (c • W) = c * herm3 Z W := by
  simp only [herm3, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma hasDerivAt_herm3 {a b : ℝ → Fin 3 → ℂ} {a' b' : Fin 3 → ℂ} {s : ℝ}
    (ha : HasDerivAt a a' s) (hb : HasDerivAt b b' s) :
    HasDerivAt (fun t => herm3 (a t) (b t)) (herm3 a' (b s) + herm3 (a s) b') s := by
  have h : ∀ i, HasDerivAt (fun t => conj (a t i) * b t i)
      (conj (a' i) * b s i + conj (a s i) * b' i) s := fun i =>
    ((hasDerivAt_pi.1 ha i).star.mul (hasDerivAt_pi.1 hb i)).congr_deriv (by simp)
  have := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => h i)
  have e : herm3 a' (b s) + herm3 (a s) b' =
      ∑ i, (conj (a' i) * b s i + conj (a s i) * b' i) := by
    rw [Finset.sum_add_distrib]; rfl
  rw [e]; exact this

lemma hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {s : ℝ} (h : HasDerivAt f f' s) :
    HasDerivAt (fun t => (f t).im) f'.im s :=
  (imCLM.hasFDerivAt.comp_hasDerivAt s h)

lemma contDiff_herm3 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞}
    {a b : X → Fin 3 → ℂ} (ha : ContDiff ℝ n a) (hb : ContDiff ℝ n b) :
    ContDiff ℝ n (fun x => herm3 (a x) (b x)) := by
  unfold herm3
  refine ContDiff.sum fun i _ => ?_
  exact (conjCLE.contDiff.comp ((contDiff_apply ℝ ℂ i).comp ha)).mul
    ((contDiff_apply ℝ ℂ i).comp hb)

/-! ### The lift on `ℝ × ℝ` and its first and second derivatives -/

/-- `Zunit` as a function on `ℝ × ℝ`. -/
def ZΦ (x : ℝ × ℝ) : Fin 3 → ℂ := Zunit x.1 x.2

lemma contDiff_ZΦ : ContDiff ℝ ∞ ZΦ := contDiff_Zunit

/-- `∂_u Zunit` on `ℝ × ℝ`. -/
def D1 (x : ℝ × ℝ) : Fin 3 → ℂ := fderiv ℝ ZΦ x (1, 0)
/-- `∂_v Zunit` on `ℝ × ℝ`. -/
def D2 (x : ℝ × ℝ) : Fin 3 → ℂ := fderiv ℝ ZΦ x (0, 1)
/-- `∂_u ∂_v Zunit`. -/
def D12 (x : ℝ × ℝ) : Fin 3 → ℂ := fderiv ℝ (fderiv ℝ ZΦ) x (1, 0) (0, 1)

lemma contDiff_fderiv_ZΦ : ContDiff ℝ ∞ (fderiv ℝ ZΦ) :=
  contDiff_ZΦ.fderiv_right (m := ∞) le_rfl

lemma contDiff_D1 : ContDiff ℝ ∞ D1 := contDiff_fderiv_ZΦ.clm_apply contDiff_const
lemma contDiff_D2 : ContDiff ℝ ∞ D2 := contDiff_fderiv_ZΦ.clm_apply contDiff_const

lemma vec_hasDerivAt_u {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : ℝ × ℝ → F}
    {u v : ℝ} (h : DifferentiableAt ℝ g (u, v)) :
    HasDerivAt (fun s => g (s, v)) (fderiv ℝ g (u, v) (1, 0)) u := by
  have hl : HasDerivAt (fun s : ℝ => ((s, v) : ℝ × ℝ)) (1, 0) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u v)
  exact h.hasFDerivAt.comp_hasDerivAt u hl

lemma vec_hasDerivAt_v {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : ℝ × ℝ → F}
    {u v : ℝ} (h : DifferentiableAt ℝ g (u, v)) :
    HasDerivAt (fun t => g (u, t)) (fderiv ℝ g (u, v) (0, 1)) v := by
  have hl : HasDerivAt (fun t : ℝ => ((u, t) : ℝ × ℝ)) (0, 1) v :=
    (hasDerivAt_const v u).prodMk (hasDerivAt_id v)
  exact h.hasFDerivAt.comp_hasDerivAt v hl

lemma fderiv_evalv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] F} {x : ℝ × ℝ} (h : DifferentiableAt ℝ A x) (w c : ℝ × ℝ) :
    fderiv ℝ (fun y => A y c) x w = fderiv ℝ A x w c := by
  rw [fderiv_clm_apply h (differentiableAt_const c)]
  simp

lemma diff_ZΦ (x : ℝ × ℝ) : DifferentiableAt ℝ ZΦ x :=
  contDiff_ZΦ.differentiable (by simp) x

lemma diff_fderiv_ZΦ (x : ℝ × ℝ) : DifferentiableAt ℝ (fderiv ℝ ZΦ) x :=
  contDiff_fderiv_ZΦ.differentiable (by simp) x

lemma hasDerivAt_Zunit_u (u v : ℝ) : HasDerivAt (fun s => Zunit s v) (D1 (u, v)) u :=
  vec_hasDerivAt_u (g := ZΦ) (diff_ZΦ _)

lemma hasDerivAt_Zunit_v (u v : ℝ) : HasDerivAt (fun t => Zunit u t) (D2 (u, v)) v :=
  vec_hasDerivAt_v (g := ZΦ) (diff_ZΦ _)

lemma dZu_eq (u v : ℝ) : dZu u v = D1 (u, v) := (hasDerivAt_Zunit_u u v).deriv
lemma dZv_eq (u v : ℝ) : dZv u v = D2 (u, v) := (hasDerivAt_Zunit_v u v).deriv

lemma hasDerivAt_dZv_u (u v : ℝ) : HasDerivAt (fun s => dZv s v) (D12 (u, v)) u := by
  have hd : DifferentiableAt ℝ D2 (u, v) := contDiff_D2.differentiable (by simp) _
  have := vec_hasDerivAt_u hd
  rw [show fderiv ℝ D2 (u, v) (1, 0) = D12 (u, v) from fderiv_evalv (diff_fderiv_ZΦ _) _ _]
    at this
  simpa only [dZv_eq] using this

lemma hasDerivAt_dZu_v (u v : ℝ) : HasDerivAt (fun t => dZu u t) (D12 (u, v)) v := by
  have hd : DifferentiableAt ℝ D1 (u, v) := contDiff_D1.differentiable (by simp) _
  have := vec_hasDerivAt_v hd
  rw [show fderiv ℝ D1 (u, v) (0, 1) = D12 (u, v) by
    show fderiv ℝ (fun y => fderiv ℝ ZΦ y (1, 0)) (u, v) (0, 1) = _
    rw [fderiv_evalv (diff_fderiv_ZΦ _)]
    exact Forms.symm2 (contDiff_ZΦ.contDiffAt.of_le (by simp)) _ _] at this
  simpa only [dZu_eq] using this

lemma Zunit_unit (u v : ℝ) : herm3 (Zunit u v) (Zunit u v) = 1 := by
  rw [herm3_self, normSq3_Zunit, ofReal_one]

/-! ### `η_H` and `σ` -/

/-- `Zunit^* η_H` as a base one-form (independent of `p`). -/
def etaH : BForm := ⟨ofUV etaHu, ofUV etaHv⟩

/-- `σ` as a base two-form coefficient (independent of `p`). -/
def sigma : Coef := ofUV sigmaC

lemma etaHu_eq (u v : ℝ) : etaHu u v = (herm3 (ZΦ (u, v)) (D1 (u, v))).im / (2 * π) := by
  rw [etaHu, dZu_eq]; rfl

lemma etaHv_eq (u v : ℝ) : etaHv u v = (herm3 (ZΦ (u, v)) (D2 (u, v))).im / (2 * π) := by
  rw [etaHv, dZv_eq]; rfl

lemma sigmaC_eq' (u v : ℝ) : sigmaC u v = (herm3 (D1 (u, v)) (D2 (u, v))).im / π := by
  rw [sigmaC, dZu_eq, dZv_eq]

lemma contDiff_etaHu : ContDiff ℝ ∞ (fun x : ℝ × ℝ => etaHu x.1 x.2) := by
  simp only [etaHu_eq]
  exact ((imCLM.contDiff.comp (contDiff_herm3 contDiff_ZΦ contDiff_D1)).div_const _)

lemma contDiff_etaHv : ContDiff ℝ ∞ (fun x : ℝ × ℝ => etaHv x.1 x.2) := by
  simp only [etaHv_eq]
  exact ((imCLM.contDiff.comp (contDiff_herm3 contDiff_ZΦ contDiff_D2)).div_const _)

lemma contDiff_sigmaC : ContDiff ℝ ∞ (fun x : ℝ × ℝ => sigmaC x.1 x.2) := by
  simp only [sigmaC_eq']
  exact ((imCLM.contDiff.comp (contDiff_herm3 contDiff_D1 contDiff_D2)).div_const _)

/-- `∂_u etaHv` (explicit). -/
def sigFv (u v : ℝ) : ℝ :=
  (herm3 (D1 (u, v)) (D2 (u, v)) + herm3 (Zunit u v) (D12 (u, v))).im / (2 * π)

/-- `∂_v etaHu` (explicit). -/
def sigFu (u v : ℝ) : ℝ :=
  (herm3 (D2 (u, v)) (D1 (u, v)) + herm3 (Zunit u v) (D12 (u, v))).im / (2 * π)

lemma hasDerivAt_etaHv_u (u v : ℝ) : HasDerivAt (fun s => etaHv s v) (sigFv u v) u := by
  have h := hasDerivAt_im (hasDerivAt_herm3 (hasDerivAt_Zunit_u u v) (hasDerivAt_dZv_u u v))
  rw [dZv_eq] at h
  exact (h.div_const (2 * π)).congr_of_eventuallyEq (Eventually.of_forall fun s => rfl)

lemma hasDerivAt_etaHu_v (u v : ℝ) : HasDerivAt (fun t => etaHu u t) (sigFu u v) v := by
  have h := hasDerivAt_im (hasDerivAt_herm3 (hasDerivAt_Zunit_v u v) (hasDerivAt_dZu_v u v))
  rw [dZu_eq] at h
  exact (h.div_const (2 * π)).congr_of_eventuallyEq (Eventually.of_forall fun s => rfl)

/-- **`d(Zunit^* η_H) = σ`** (`lem:fer-sigma`). -/
theorem d_etaH (u v p : ℝ) : etaH.dC u v p = sigma u v p := by
  simp only [BForm.dC, etaH, sigma, ofUV, pu, pv]
  rw [(hasDerivAt_etaHv_u u v).deriv, (hasDerivAt_etaHu_v u v).deriv, sigmaC_eq', sigFv, sigFu,
    herm3_swap (D1 (u, v))]
  simp only [add_im, conj_im]
  field_simp
  ring

/-! ### The deck transformations act by unit phases -/

lemma torusZ_add_one_left (u v : ℝ) : torusZ (u + 1) v = torusZ u v + 1 := by
  simp [torusZ]; ring

lemma torusZ_add_one_right (u v : ℝ) : torusZ u (v + 1) = torusZ u v + tau := by
  simp [torusZ]; ring

lemma normSq3_smul (c : ℂ) (Z : Fin 3 → ℂ) : normSq3 (c • Z) = ‖c‖ ^ 2 * normSq3 Z := by
  simp only [normSq3, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]

/-- `Zunit (u + 1) v = −Zunit u v`. -/
theorem Zunit_add_one_left (u v : ℝ) : Zunit (u + 1) v = (-1 : ℂ) • Zunit u v := by
  simp only [Zunit, torusZ_add_one_left, Zraw_add_one, normSq3_smul, norm_neg, norm_one,
    one_pow, one_mul]
  rw [smul_comm]

/-- The automorphy factor of `Zraw` under `z ↦ z + τ`, at `z = u + vτ`. -/
def autE (u v : ℝ) : ℂ := thetaFactor (π * torusZ u v) ^ 3

lemma autE_ne_zero (u v : ℝ) : autE u v ≠ 0 := pow_ne_zero 3 (thetaFactor_ne_zero _)

/-- The unit phase of the deck transformation `v ↦ v + 1`. -/
def phaseV (u v : ℝ) : ℂ := (‖autE u v‖⁻¹ : ℝ) • autE u v

lemma norm_phaseV (u v : ℝ) : ‖phaseV u v‖ = 1 := by
  have := autE_ne_zero u v
  rw [phaseV, norm_smul, Real.norm_of_nonneg (by positivity),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr this)]

/-- `Zunit u (v + 1) = φ(u, v) • Zunit u v` with the unit phase `φ = e/|e|`. -/
theorem Zunit_add_one_right (u v : ℝ) : Zunit u (v + 1) = phaseV u v • Zunit u v := by
  have hpos := normSq3_pos (Zraw_ne_zero (torusZ u v))
  have he := autE_ne_zero u v
  have hn : 0 < ‖autE u v‖ := norm_pos_iff.mpr he
  ext i
  simp only [Zunit, torusZ_add_one_right, Zraw_add_tau, phaseV, normSq3_smul, Pi.smul_apply,
    smul_eq_mul, Complex.real_smul]
  rw [show thetaFactor (π * torusZ u v) ^ 3 = autE u v from rfl, Real.sqrt_mul (by positivity),
    Real.sqrt_sq hn.le]
  push_cast
  field_simp

lemma conj_mul_self_of_norm_one {c : ℂ} (h : ‖c‖ = 1) : conj c * c = 1 := by
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, h]; simp

/-! ### The `λ`-expression of a framed curve -/

/-- `λ(Z, Z') = (Im⟨Z, Z'⟩ − Im(Z'₀/Z₀)) / 2π`, the value of `λ_C = η_H − d(arg Z₀)/2π` on a
tangent vector with `dZ = Z'`. -/
def lamExpr (Z Z' : Fin 3 → ℂ) : ℝ := ((herm3 Z Z').im - (Z' 0 / Z 0).im) / (2 * π)

/-- `λ` is invariant under multiplication by a unit phase (with its derivative). -/
theorem lamExpr_smul {Z Z' : Fin 3 → ℂ} {c c' : ℂ} (hZ : herm3 Z Z = 1) (hc : ‖c‖ = 1)
    (h0 : Z 0 ≠ 0) : lamExpr (c • Z) (c' • Z + c • Z') = lamExpr Z Z' := by
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc
  have hcc := conj_mul_self_of_norm_one hc
  have hconj : conj c = c⁻¹ := eq_inv_of_mul_eq_one_left hcc
  unfold lamExpr
  rw [herm3_add_right, herm3_smul_left, herm3_smul_left, herm3_smul_right, herm3_smul_right, hZ]
  congr 1
  have e1 : conj c * (c' * 1) + conj c * (c * herm3 Z Z') = c' / c + herm3 Z Z' := by
    rw [hconj]; field_simp
  have e2 : (c' • Z + c • Z') 0 / (c • Z) 0 = c' / c + Z' 0 / Z 0 := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; field_simp
  rw [e1, e2, add_im, add_im]; ring

/-- `η`-expression `Im⟨Z, Z'⟩ / 2π` under a unit phase. -/
theorem etaExpr_smul {Z Z' : Fin 3 → ℂ} {c c' : ℂ} (hZ : herm3 Z Z = 1) (hc : ‖c‖ = 1) :
    (herm3 (c • Z) (c' • Z + c • Z')).im / (2 * π) =
      (conj c * c').im / (2 * π) + (herm3 Z Z').im / (2 * π) := by
  rw [herm3_add_right, herm3_smul_left, herm3_smul_left, herm3_smul_right, herm3_smul_right, hZ,
    mul_one, ← mul_assoc (conj c) c, conj_mul_self_of_norm_one hc, one_mul, add_im, add_div]

/-! ### `λ_C` -/

/-- `du`-coefficient of `λ_C = η_H − (1/2π) Im(dZ₀/Z₀)`. -/
def lambdaCu (u v : ℝ) : ℝ := lamExpr (Zunit u v) (dZu u v)

/-- `dv`-coefficient of `λ_C`. -/
def lambdaCv (u v : ℝ) : ℝ := lamExpr (Zunit u v) (dZv u v)

/-- **The one-form `λ_C`** (`def:fer-frame`), `γ_σ = λ_C`, `a_𝒜 = −3λ_C`. -/
def lambdaC : BForm := ⟨ofUV lambdaCu, ofUV lambdaCv⟩

lemma lambdaCu_eq (u v : ℝ) :
    lambdaCu u v = etaHu u v - (dZu u v 0 / Zunit u v 0).im / (2 * π) := by
  rw [lambdaCu, lamExpr, etaHu]; ring

lemma lambdaCv_eq (u v : ℝ) :
    lambdaCv u v = etaHv u v - (dZv u v 0 / Zunit u v 0).im / (2 * π) := by
  rw [lambdaCv, lamExpr, etaHv]; ring

/-- The set `{Z₀ ≠ 0}` on the cover. -/
def ZnzSet : Set (ℝ × ℝ) := {x | Zunit x.1 x.2 0 ≠ 0}

lemma isOpen_ZnzSet : IsOpen ZnzSet :=
  isOpen_ne_fun ((continuous_apply 0).comp contDiff_ZΦ.continuous) continuous_const

lemma contDiffOn_lambdaCu : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => lambdaCu x.1 x.2) ZnzSet := by
  simp only [lambdaCu_eq, dZu_eq]
  refine contDiff_etaHu.contDiffOn.sub ?_
  refine (imCLM.contDiff.comp_contDiffOn (f := fun x : ℝ × ℝ => D1 x 0 / ZΦ x 0) ?_).div_const _
  simp only [div_eq_mul_inv]
  exact ((contDiff_apply ℝ ℂ 0).comp contDiff_D1).contDiffOn.mul
    (((contDiff_apply ℝ ℂ 0).comp contDiff_ZΦ).contDiffOn.inv fun x hx => hx)

lemma contDiffOn_lambdaCv : ContDiffOn ℝ ∞ (fun x : ℝ × ℝ => lambdaCv x.1 x.2) ZnzSet := by
  simp only [lambdaCv_eq, dZv_eq]
  refine contDiff_etaHv.contDiffOn.sub ?_
  refine (imCLM.contDiff.comp_contDiffOn (f := fun x : ℝ × ℝ => D2 x 0 / ZΦ x 0) ?_).div_const _
  simp only [div_eq_mul_inv]
  exact ((contDiff_apply ℝ ℂ 0).comp contDiff_D2).contDiffOn.mul
    (((contDiff_apply ℝ ℂ 0).comp contDiff_ZΦ).contDiffOn.inv fun x hx => hx)

/-- **`dλ_C = σ`** on `{Z₀ ≠ 0}` (`lem:fer-frame`). -/
theorem d_lambdaC {u v : ℝ} (h0 : Zunit u v 0 ≠ 0) (p : ℝ) :
    lambdaC.dC u v p = sigma u v p := by
  have hA : HasDerivAt (fun s => (dZv s v 0 / Zunit s v 0).im)
      ((D12 (u, v) 0 * Zunit u v 0 - D2 (u, v) 0 * D1 (u, v) 0) / Zunit u v 0 ^ 2).im u := by
    have := hasDerivAt_im (((hasDerivAt_pi.1 (hasDerivAt_dZv_u u v) 0)).div
      (hasDerivAt_pi.1 (hasDerivAt_Zunit_u u v) 0) h0)
    rwa [dZv_eq] at this
  have hB : HasDerivAt (fun t => (dZu u t 0 / Zunit u t 0).im)
      ((D12 (u, v) 0 * Zunit u v 0 - D1 (u, v) 0 * D2 (u, v) 0) / Zunit u v 0 ^ 2).im v := by
    have := hasDerivAt_im (((hasDerivAt_pi.1 (hasDerivAt_dZu_v u v) 0)).div
      (hasDerivAt_pi.1 (hasDerivAt_Zunit_v u v) 0) h0)
    rwa [dZu_eq] at this
  have h1 : HasDerivAt (fun s => lambdaCv s v) _ u :=
    ((hasDerivAt_etaHv_u u v).sub (hA.div_const (2 * π))).congr_of_eventuallyEq
      (Eventually.of_forall fun s => lambdaCv_eq s v)
  have h2 : HasDerivAt (fun t => lambdaCu u t) _ v :=
    ((hasDerivAt_etaHu_v u v).sub (hB.div_const (2 * π))).congr_of_eventuallyEq
      (Eventually.of_forall fun t => lambdaCu_eq u t)
  have he := d_etaH u v p
  simp only [BForm.dC, etaH, sigma, ofUV, pu, pv, lambdaC] at he ⊢
  rw [h1.deriv, h2.deriv, ← he, (hasDerivAt_etaHv_u u v).deriv, (hasDerivAt_etaHu_v u v).deriv,
    mul_comm (D2 (u, v) 0), sigFv, sigFu]
  ring

/-! ### Periodicity of `λ_C` -/

lemma differentiable_thetaFactor : Differentiable ℂ thetaFactor := by
  intro ζ; unfold thetaFactor; fun_prop

lemma differentiable_autE : Differentiable ℝ (fun x : ℝ × ℝ => autE x.1 x.2) := by
  have h1 : Differentiable ℂ (fun ζ : ℂ => thetaFactor ζ ^ 3) := differentiable_thetaFactor.pow 3
  have h2 : Differentiable ℝ (fun x : ℝ × ℝ => (π : ℂ) * torusZ x.1 x.2) := by
    unfold torusZ
    exact (((ofRealCLM.differentiable.comp differentiable_fst).add
      ((ofRealCLM.differentiable.comp differentiable_snd).mul_const _)).const_mul _)
  exact (h1.restrictScalars ℝ).comp h2

lemma phaseV_differentiableAt (u v : ℝ) :
    DifferentiableAt ℝ (fun x : ℝ × ℝ => phaseV x.1 x.2) (u, v) := by
  have hN : DifferentiableAt ℝ (fun x : ℝ × ℝ => ‖autE x.1 x.2‖⁻¹) (u, v) :=
    ((differentiable_autE (u, v)).norm ℝ (autE_ne_zero u v)).inv
      (norm_ne_zero_iff.mpr (autE_ne_zero u v))
  exact hN.smul (differentiable_autE (u, v))

/-- **`λ_C` descends to the torus** (`lem:fer-frame`): it is `1`-periodic in `u` and `v`
on `{Z₀ ≠ 0}` (the deck transformations multiply `Zunit` by unit phases). -/
theorem lambdaC_descends {u v : ℝ} (h0 : Zunit u v 0 ≠ 0) :
    lambdaCu (u + 1) v = lambdaCu u v ∧ lambdaCv (u + 1) v = lambdaCv u v ∧
      lambdaCu u (v + 1) = lambdaCu u v ∧ lambdaCv u (v + 1) = lambdaCv u v := by
  have hneg : ‖(-1 : ℂ)‖ = 1 := by simp
  -- shift in `u`
  have eU : ∀ v', (fun s => Zunit (s + 1) v') = fun s => (-1 : ℂ) • Zunit s v' := fun v' =>
    funext fun s => Zunit_add_one_left s v'
  have hu1 : dZu (u + 1) v = (0 : ℂ) • Zunit u v + (-1 : ℂ) • dZu u v := by
    rw [zero_smul, zero_add, dZu, ← deriv_comp_add_const, eU, dZu_eq]
    exact ((hasDerivAt_Zunit_u u v).const_smul (-1 : ℂ)).deriv
  have hu2 : dZv (u + 1) v = (0 : ℂ) • Zunit u v + (-1 : ℂ) • dZv u v := by
    rw [zero_smul, zero_add, dZv]
    simp only [Zunit_add_one_left]
    rw [dZv_eq]
    exact ((hasDerivAt_Zunit_v u v).const_smul (-1 : ℂ)).deriv
  -- shift in `v`
  obtain ⟨a, ha⟩ : ∃ a, HasDerivAt (fun s => phaseV s v) a u :=
    ⟨_, (vec_hasDerivAt_u (phaseV_differentiableAt u v))⟩
  obtain ⟨b, hb⟩ : ∃ b, HasDerivAt (fun t => phaseV u t) b v :=
    ⟨_, (vec_hasDerivAt_v (phaseV_differentiableAt u v))⟩
  have hv1 : dZu u (v + 1) = a • Zunit u v + phaseV u v • dZu u v := by
    rw [dZu]; simp only [Zunit_add_one_right]
    exact (ha.smul (hasDerivAt_Zunit_u u v)).deriv.trans (by rw [dZu_eq]; abel)
  have hv2 : dZv u (v + 1) = b • Zunit u v + phaseV u v • dZv u v := by
    rw [dZv, ← deriv_comp_add_const]; simp only [Zunit_add_one_right]
    exact (hb.smul (hasDerivAt_Zunit_v u v)).deriv.trans (by rw [dZv_eq]; abel)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lambdaCu, lambdaCu, hu1, Zunit_add_one_left]
    exact lamExpr_smul (Zunit_unit u v) hneg h0
  · rw [lambdaCv, lambdaCv, hu2, Zunit_add_one_left]
    exact lamExpr_smul (Zunit_unit u v) hneg h0
  · rw [lambdaCu, lambdaCu, hv1, Zunit_add_one_right]
    exact lamExpr_smul (Zunit_unit u v) (norm_phaseV u v) h0
  · rw [lambdaCv, lambdaCv, hv2, Zunit_add_one_right]
    exact lamExpr_smul (Zunit_unit u v) (norm_phaseV u v) h0

/-! ### `∫ σ = 3` -/

lemma etaHv_add_one_left (u v : ℝ) : etaHv (u + 1) v = etaHv u v := by
  have hu2 : dZv (u + 1) v = (0 : ℂ) • Zunit u v + (-1 : ℂ) • dZv u v := by
    rw [zero_smul, zero_add, dZv]
    simp only [Zunit_add_one_left]
    rw [dZv_eq]
    exact ((hasDerivAt_Zunit_v u v).const_smul (-1 : ℂ)).deriv
  rw [etaHv, etaHv, hu2, Zunit_add_one_left, etaExpr_smul (Zunit_unit u v) (by simp)]
  simp

/-- The phase along `v = 0`: `φ(u) = −exp(−3πiτ − 6πiu) / exp(3π Im τ)`. -/
lemma phaseV_zero (u : ℝ) :
    phaseV u 0 = -cexp (-(3 * π * I * tau) - 6 * π * I * u) / (Real.exp (3 * π * tau.im) : ℂ) := by
  have he : autE u 0 = -cexp (-(3 * π * I * tau) - 6 * π * I * u) := by
    simp only [autE, thetaFactor, torusZ, ofReal_zero, zero_mul, add_zero]
    rw [neg_pow, ← Complex.exp_nat_mul]
    have : ((3 : ℕ) : ℂ) * (-(↑π * I * tau) - 2 * I * (↑π * ↑u)) =
        -(3 * ↑π * I * tau) - 6 * ↑π * I * ↑u := by push_cast; ring
    rw [this]; ring
  have hn : ‖autE u 0‖ = Real.exp (3 * π * tau.im) := by
    rw [he, norm_neg, Complex.norm_exp]
    congr 1
    simp only [sub_re, neg_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_im]
    norm_num <;> ring
  rw [phaseV, hn, he, Complex.real_smul]
  push_cast
  ring

lemma hasDerivAt_phaseV_zero (u : ℝ) :
    HasDerivAt (fun s => phaseV s 0) (-(6 * π * I) * phaseV u 0) u := by
  have h : HasDerivAt (fun s : ℝ => (-(3 * π * I * tau) - 6 * π * I * (s : ℂ)))
      (-(6 * π * I)) u := by
    have := ((hasDerivAt_id u).ofReal_comp.const_mul (6 * π * I)).const_sub (-(3 * π * I * tau))
    simpa using this
  have := ((h.cexp).neg).div_const (Real.exp (3 * π * tau.im) : ℂ)
  convert this using 1
  · funext s; exact phaseV_zero s
  · rw [phaseV_zero]; ring

lemma etaHu_one (u : ℝ) : etaHu u 1 = etaHu u 0 - 3 := by
  have hv1 : dZu u (0 + 1) = (-(6 * π * I) * phaseV u 0) • Zunit u 0 +
      phaseV u 0 • dZu u 0 := by
    rw [dZu]; simp only [Zunit_add_one_right]
    exact ((hasDerivAt_phaseV_zero u).smul (hasDerivAt_Zunit_u u 0)).deriv.trans
      (by rw [dZu_eq]; abel)
  have e : etaHu u 1 = etaHu u (0 + 1) := by norm_num
  rw [e, etaHu, hv1, Zunit_add_one_right, etaExpr_smul (Zunit_unit u 0) (norm_phaseV u 0), etaHu]
  have : conj (phaseV u 0) * (-(6 * π * I) * phaseV u 0) = -(6 * π * I) := by
    rw [mul_left_comm, conj_mul_self_of_norm_one (norm_phaseV u 0), mul_one]
  rw [this]
  simp only [neg_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_re]
  norm_num
  field_simp
  ring

lemma contDiff_D12 : ContDiff ℝ ∞ D12 :=
  ((contDiff_fderiv_ZΦ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).clm_apply
    contDiff_const

lemma continuous_sigFv : Continuous (fun x : ℝ × ℝ => sigFv x.1 x.2) :=
  ((imCLM.contDiff.comp ((contDiff_herm3 contDiff_D1 contDiff_D2).add
    (contDiff_herm3 contDiff_ZΦ contDiff_D12))).div_const _).continuous

lemma continuous_sigFu : Continuous (fun x : ℝ × ℝ => sigFu x.1 x.2) :=
  ((imCLM.contDiff.comp ((contDiff_herm3 contDiff_D2 contDiff_D1).add
    (contDiff_herm3 contDiff_ZΦ contDiff_D12))).div_const _).continuous

lemma sigmaC_eq_sig (u v : ℝ) : sigmaC u v = sigFv u v - sigFu u v := by
  have := d_etaH u v 0
  simp only [BForm.dC, etaH, sigma, ofUV, pu, pv] at this
  rw [← this, (hasDerivAt_etaHv_u u v).deriv, (hasDerivAt_etaHu_v u v).deriv]

attribute [local irreducible] etaHu etaHv sigFu sigFv in
lemma integral_sigFv (v : ℝ) : ∫ u in (0 : ℝ)..1, sigFv u v = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun s => etaHv s v)
    (fun u _ => hasDerivAt_etaHv_u u v)
    ((continuous_sigFv.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)]
  have := etaHv_add_one_left 0 v
  rw [zero_add] at this
  simp [this]

attribute [local irreducible] etaHu etaHv sigFu sigFv in
lemma hasDerivAt_integral_etaHu (v : ℝ) :
    HasDerivAt (fun t => ∫ u in (0 : ℝ)..1, etaHu u t) (∫ u in (0 : ℝ)..1, sigFu u v) v := by
  have hgs : ContDiff ℝ ∞ (fun y : ℝ × ℝ => etaHu y.2 y.1) :=
    contDiff_etaHu.comp (contDiff_snd.prodMk contDiff_fst)
  have hg : ContDiffOn ℝ 1 (fun y : ℝ × ℝ => etaHu y.2 y.1) (univ ×ˢ univ) :=
    (hgs.of_le (by exact_mod_cast le_top)).contDiffOn
  have := hasDerivAt_integral_param isOpen_univ hg (mem_univ v) 0 1
  have e : ∫ u in (0 : ℝ)..1, sigFu u v =
      ∫ w in (0 : ℝ)..1, fderiv ℝ (fun y : ℝ × ℝ => etaHu y.2 y.1) (v, w) (1, 0) := by
    refine intervalIntegral.integral_congr fun u _ => ?_
    have hd : DifferentiableAt ℝ (fun y : ℝ × ℝ => etaHu y.2 y.1) (v, u) :=
      hgs.differentiable (by simp) _
    exact (hasDerivAt_etaHu_v u v).unique (vec_hasDerivAt_u hd)
  rw [e]; exact this

attribute [local irreducible] etaHu etaHv sigFu sigFv in
lemma integral_sigFu : ∫ v in (0 : ℝ)..1, ∫ u in (0 : ℝ)..1, sigFu u v = -3 := by
  have hcu : Continuous (fun x : ℝ × ℝ => etaHu x.1 x.2) := contDiff_etaHu.continuous
  have hGc : Continuous (fun v => ∫ u in (0 : ℝ)..1, sigFu u v) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun v u => sigFu u v) (continuous_sigFu.comp continuous_swap) 0 1
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t => ∫ u in (0 : ℝ)..1, etaHu u t) (f' := fun v => ∫ u in (0 : ℝ)..1, sigFu u v)
    (fun v _ => hasDerivAt_integral_etaHu v) (hGc.intervalIntegrable _ _)]
  have e : ∫ u in (0 : ℝ)..1, etaHu u 1 = ∫ u in (0 : ℝ)..1, (etaHu u 0 - 3) :=
    intervalIntegral.integral_congr fun u _ => etaHu_one u
  have h0 : IntervalIntegrable (fun u => etaHu u 0) volume 0 1 :=
    (hcu.comp (continuous_id.prodMk (continuous_const (y := (0 : ℝ))))).intervalIntegrable 0 1
  rw [e, intervalIntegral.integral_sub h0 intervalIntegrable_const]
  simp

/-- **`∫_{[0,1]²} σ = 3`** (`lem:fer-sigma`), by Stokes on the unit square. -/
theorem integral_sigma : torusInt sigmaC = 3 := by
  have hint : ∀ v, ∫ u in (0 : ℝ)..1, sigmaC u v =
      (∫ u in (0 : ℝ)..1, sigFv u v) - ∫ u in (0 : ℝ)..1, sigFu u v := by
    intro v
    simp only [sigmaC_eq_sig]
    exact intervalIntegral.integral_sub
      ((continuous_sigFv.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
      ((continuous_sigFu.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
  unfold torusInt
  simp only [hint, integral_sigFv, zero_sub]
  rw [intervalIntegral.integral_neg, integral_sigFu]; norm_num

/-! ### The frame over `𝒜⁺` (`def:fer-frame`, `lem:fer-frame`) -/

/-- **The frame `(Z₀/|Z₀|)³`** relative to the global frame `Zunit`: the point `[Zunit, w]` has
`𝒜⁺`-fibre coordinate `u_𝒜 = conj(frameA) · w` (`frameA_coord`), defined where `Z₀ ≠ 0`. -/
def frameA (u v : ℝ) : ℂ := (Zunit u v 0 / ((‖Zunit u v 0‖ : ℝ) : ℂ)) ^ 3

lemma norm_frameA {u v : ℝ} (h0 : Zunit u v 0 ≠ 0) : ‖frameA u v‖ = 1 := by
  rw [frameA, norm_pow, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr h0), one_pow]

lemma im_logDeriv_frame {Z : ℝ → ℂ} {Z' : ℂ} {s : ℝ} (hZ : HasDerivAt Z Z' s) (h0 : Z s ≠ 0) :
    ∃ F', HasDerivAt (fun t => (Z t / ((‖Z t‖ : ℝ) : ℂ)) ^ 3) F' s ∧
      (F' / (Z s / ((‖Z s‖ : ℝ) : ℂ)) ^ 3).im = 3 * (Z' / Z s).im := by
  have hN0 : ‖Z s‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  obtain ⟨N', hN⟩ : ∃ N', HasDerivAt (fun t => ‖Z t‖) N' s :=
    ⟨_, (hZ.differentiableAt.norm ℝ h0).hasDerivAt⟩
  have hNc : HasDerivAt (fun t => ((‖Z t‖ : ℝ) : ℂ)) (N' : ℂ) s := hN.ofReal_comp
  have hq := (hZ.div hNc (by exact_mod_cast hN0)).pow 3
  refine ⟨_, hq, ?_⟩
  have hN0' : ((‖Z s‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN0
  have e : ((3 : ℕ) : ℂ) * (Z s / ((‖Z s‖ : ℝ) : ℂ)) ^ (3 - 1) *
      ((Z' * ((‖Z s‖ : ℝ) : ℂ) - Z s * (N' : ℂ)) / ((‖Z s‖ : ℝ) : ℂ) ^ 2) /
      (Z s / ((‖Z s‖ : ℝ) : ℂ)) ^ 3 = 3 * (Z' / Z s) - ((3 * N' / ‖Z s‖ : ℝ) : ℂ) := by
    push_cast
    field_simp
  rw [show (Z / fun t => ((‖Z t‖ : ℝ) : ℂ)) s = Z s / ((‖Z s‖ : ℝ) : ℂ) from rfl, e, sub_im, ofReal_im, sub_zero]
  simp

/-- **The angular form in the `𝒜⁺` frame** (`lem:fer-frame`): with `θ = θ_𝒜 + arg(frameA)/2π`,
`a_𝒜 = −3λ_C` and `a_loc = −3η_H` differ by `d(arg frameA)/2π`, so
`α = dθ + a_loc = dθ_𝒜 + a_𝒜`. Stated for both coefficients where `Z₀ ≠ 0`. -/
theorem angularForm_frameA {u v : ℝ} (h0 : Zunit u v 0 ≠ 0) :
    -3 * lambdaCu u v = -3 * etaHu u v +
        (deriv (fun s => frameA s v) u / frameA u v).im / (2 * π) ∧
      -3 * lambdaCv u v = -3 * etaHv u v +
        (deriv (fun t => frameA u t) v / frameA u v).im / (2 * π) := by
  obtain ⟨F1, h1, e1⟩ := im_logDeriv_frame (hasDerivAt_pi.1 (hasDerivAt_Zunit_u u v) 0) h0
  obtain ⟨F2, h2, e2⟩ := im_logDeriv_frame (hasDerivAt_pi.1 (hasDerivAt_Zunit_v u v) 0) h0
  constructor
  · rw [show (fun s => frameA s v) = fun s => (Zunit s v 0 / ((‖Zunit s v 0‖ : ℝ) : ℂ)) ^ 3
      from rfl, h1.deriv, show frameA u v = (Zunit u v 0 / ((‖Zunit u v 0‖ : ℝ) : ℂ)) ^ 3 from rfl,
      e1, lambdaCu_eq, dZu_eq]
    ring
  · rw [show (fun t => frameA u t) = fun t => (Zunit u t 0 / ((‖Zunit u t 0‖ : ℝ) : ℂ)) ^ 3
      from rfl, h2.deriv, show frameA u v = (Zunit u v 0 / ((‖Zunit u v 0‖ : ℝ) : ℂ)) ^ 3 from rfl,
      e2, lambdaCv_eq, dZv_eq]
    ring

end SymplecticPacking.Bundle
