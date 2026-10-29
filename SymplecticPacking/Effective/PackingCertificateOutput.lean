import SymplecticPacking.Effective.PackingCertificateField
import SymplecticPacking.General.CompileOutput

/-!
# Properties of the finite output Hamiltonian

Finite output: smoothness, uniform spatial support and global integral curves.
-/

noncomputable section
namespace SymplecticPacking.Effective.PackingPolynomial
open Set Metric Problem
open scoped ContDiff Topology NNReal
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def output (n B : ℕ) (e : Expr) : General.Compile.FiniteOutput n :=
  ⟨B,toPolynomial (2*n+1) e⟩

theorem output_eq (n B : ℕ) (e : Expr) (t : ℝ) (z : E n) :
    (output n B e).hamiltonian t z=General.Compile.boxCut n B z*
      realEval (2*n+1) e (Fin.cons t (fun j => z j)) := by
  change General.Compile.boxCut n B z*General.Compile.evalPoly
    (toPolynomial (2*n+1) e) t z = _
  rw [General.Compile.evalPoly, ← MvPolynomial.eval₂_eq_eval_map, eval_toPolynomial]

theorem smooth_point (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × E n => (Fin.cons p.1 (fun j => p.2 j) : Fin (2*n+1) → ℝ)) := by
  rw [contDiff_pi]
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact contDiff_fst
  · exact (EuclideanSpace.proj j : E n →L[ℝ] ℝ).contDiff.comp contDiff_snd

theorem output_smooth (n B : ℕ) (e : Expr) :
    ContDiff ℝ ∞ (fun p : ℝ × E n => (output n B e).hamiltonian p.1 p.2) := by
  have heq : (fun p : ℝ × E n => (output n B e).hamiltonian p.1 p.2)=
      (fun p : ℝ × E n => General.Compile.boxCut n B p.2*
        realEval (2*n+1) e (Fin.cons p.1 (fun j => p.2 j))) :=
    funext fun p => output_eq n B e p.1 p.2
  rw [heq]
  exact ((General.Compile.contDiff_boxCut (n := n) (B:ℝ)).comp contDiff_snd).mul
    ((smooth (2*n+1) e).comp (smooth_point n))

theorem output_support (n B : ℕ) (e : Expr) (hB : 0<B) :
    ∀ t (z : E n), (2*n:ℝ)*(3*(B:ℝ)/4)<‖z‖ → (output n B e).hamiltonian t z=0 := by
  have hBr : (0:ℝ)<B := by exact_mod_cast hB
  apply General.Compile.support_of_coords (by positivity : (0:ℝ)≤3*(B:ℝ)/4)
  rintro t z ⟨j,hj⟩
  rw [output_eq, General.Compile.boxCut_eq_zero hBr hj, zero_mul]

/-- These are integral curves of the *output Hamiltonian on all real
times*. Time clamping appears only in the internal finite verifier. -/
theorem output_exists_global (n B : ℕ) (e : Expr) (hB : 0<B) (x : E n) :
    ∃ γ : ℝ → E n, γ 0=x ∧ IsIntegralCurve γ (Problem.hamVF (output n B e).hamiltonian) :=
  General.Compile.exists_integralCurve_global (output_smooth n B e)
    (output_support n B e hB) x

theorem polynomial_partial (n : ℕ) (e : Expr) (t : ℝ) (z : E n) (j : Fin (2*n)) :
    Problem.partialDeriv (fun w : E n => realEval (2*n+1) e
      (Fin.cons t (fun l => w l))) j z =
      realEval (2*n+1) (derivative j.succ.val e) (Fin.cons t (fun l => z l)) := by
  letI : ContinuousSMul ℝ (E n) := IsBoundedSMul.continuousSMul
  let L : E n →L[ℝ] (Fin (2*n+1) → ℝ) := ContinuousLinearMap.pi
    (Fin.cases 0 (fun l => (EuclideanSpace.proj l : E n →L[ℝ] ℝ)))
  have hψ : HasFDerivAt (fun w : E n => (Fin.cons t (fun l => w l) : Fin (2*n+1) → ℝ)) L z := by
    apply hasFDerivAt_pi.mpr
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [L] using hasFDerivAt_const t z
    · simpa [L] using (EuclideanSpace.proj i : E n →L[ℝ] ℝ).hasFDerivAt
  have he : HasFDerivAt (realEval (2*n+1) e)
      (fderiv ℝ (realEval (2*n+1) e) (Fin.cons t (fun l => z l)))
      (Fin.cons t (fun l => z l)) :=
    ((smooth (2*n+1) e).differentiable (by simp)
      (Fin.cons t (fun l => z l))).hasFDerivAt
  have hd : HasFDerivAt
      (fun w : E n => realEval (2*n+1) e (Fin.cons t (fun l => w l)))
      ((fderiv ℝ (realEval (2*n+1) e) (Fin.cons t (fun l => z l))).comp L) z := by
    simpa only [Function.comp_def] using he.comp z hψ
  have hfd : fderiv ℝ (fun w : E n => realEval (2*n+1) e
      (Fin.cons t (fun l => w l))) z =
      (fderiv ℝ (realEval (2*n+1) e) (Fin.cons t (fun l => z l))).comp L := hd.fderiv
  unfold Problem.partialDeriv
  rw [hfd]
  have hL : L (EuclideanSpace.single j 1) = Pi.single j.succ 1 := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [L, Pi.single_apply]
  change (fderiv ℝ (realEval (2*n+1) e) (Fin.cons t (fun l => z l)))
    (L (EuclideanSpace.single j 1)) = _
  rw [hL]
  exact derivative_correct (2*n+1) e _ j.succ

theorem boxCut_eventually_one (n B : ℕ) (hB : 0<B) {z : E n}
    (hz : ∀ j, |z j|<(B:ℝ)/2) :
    General.Compile.boxCut n B =ᶠ[𝓝 z] (fun _ => 1) := by
  have hs : ∀ᶠ w : E n in 𝓝 z, ∀ j, |w j|<(B:ℝ)/2 := by
    apply Filter.eventually_all.mpr
    intro j
    exact (isOpen_lt ((EuclideanSpace.proj j : E n →L[ℝ] ℝ).continuous.abs)
      continuous_const).mem_nhds (hz j)
  filter_upwards [hs] with w hw
  exact General.Compile.boxCut_eq_one (by exact_mod_cast hB) (fun j => (hw j).le)

/-- On the certified plateau, the verifier's clipped field is exactly the
Hamiltonian vector field of the delivered finite output. -/
theorem field_eq_output_of_plateau (n B : ℕ) (e : Expr) (hB : 0<B)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) {z : E n} (hz : ∀ j, |z j|<(B:ℝ)/2) :
    (WithLp.toLp 2 (field n B e t (fun j => z j)) : E n)=
      Problem.hamVF (output n B e).hamiltonian t z := by
  letI : ContinuousSMul ℝ (E n) := IsBoundedSMul.continuousSMul
  have hpt : clippedPoint (2*n) B t (fun j => z j)=Fin.cons t (fun j => z j) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact clip_eq ht
    · exact clip_eq ⟨by linarith [(abs_lt.mp (hz i)).1], (abs_lt.mp (hz i)).2.le⟩
  have hev : (output n B e).hamiltonian t =ᶠ[𝓝 z]
      (fun w : E n => realEval (2*n+1) e (Fin.cons t (fun j => w j))) := by
    filter_upwards [boxCut_eventually_one n B hB hz] with w hw
    rw [output_eq, hw, one_mul]
  have hfd : fderiv ℝ ((output n B e).hamiltonian t) z =
      fderiv ℝ (fun w : E n => realEval (2*n+1) e
        (Fin.cons t (fun j => w j))) z := hev.fderiv_eq (𝕜 := ℝ)
  apply PiLp.ext
  intro i
  simp only [field, hpt, PiLp.toLp_apply, Problem.hamVF]
  split_ifs with hi
  · have hh := polynomial_partial n e t z (⟨i.val+n, by omega⟩:Fin (2*n))
    unfold Problem.partialDeriv at hh ⊢
    rw [hfd]
    exact hh.symm
  · have hh := polynomial_partial n e t z
      (⟨i.val-n, by have := i.isLt; omega⟩:Fin (2*n))
    unfold Problem.partialDeriv at hh ⊢
    rw [hfd]
    exact congrArg Neg.neg hh.symm

end SymplecticPacking.Effective.PackingPolynomial
