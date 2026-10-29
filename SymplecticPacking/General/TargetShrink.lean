import SymplecticPacking.General.Compile
import SymplecticPacking.Effective.PackingCertificate

/-!
# Shrinking the target of a smooth packing

A fixed smooth packing has a uniform strict target margin.
-/

noncomputable section
namespace SymplecticPacking.Problem
open Set Metric Filter
open scoped Topology NNReal ContDiff

private theorem compact_capBall {n : ℕ} (s : E n) (c : ℝ) : IsCompact (capBall s c) := by
  have hc : IsClosed (capBall s c) := isClosed_le
    (by fun_prop : Continuous (fun y : E n => Real.pi*‖y-s‖^2)) continuous_const
  refine Metric.isCompact_of_isClosed_isBounded hc ?_
  apply (Metric.isBounded_closedBall (x:=s) (r:=Real.sqrt (|c|/Real.pi))).subset
  intro y hy
  rw [mem_closedBall,dist_eq_norm]
  apply Real.le_sqrt_of_sq_le
  apply (le_div_iff₀ Real.pi_pos).mpr
  change Real.pi*‖y-s‖^2 ≤ c at hy
  nlinarith [le_abs_self c]

/-- The very same Hamiltonian packs into a smaller positive capacity. Compactness
is used only to prove the uniform strict margin, never to define output data. -/
theorem PackingSpec.exists_smaller_target {n k : ℕ} {C : ℝ}
    {c : Fin k → ℝ} {s : Fin k → E n} {H : ℝ → E n → ℝ}
    (hpack : PackingSpec n k C c s H) (hC : 0 < C) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ C₀ < C ∧ PackingSpec n k C₀ c s H := by
  classical
  obtain ⟨K,hK,hHzero⟩ := hpack.compactSupport
  obtain ⟨R,hKR⟩ := hK.isBounded.subset_closedBall (0:E n)
  have hR : ∀ t (z : E n), R < ‖z‖ → H t z=0 := by
    intro t z hz
    apply hHzero t z
    intro hzK
    have hh := hKR hzK
    rw [mem_closedBall,dist_zero_right] at hh
    linarith
  obtain ⟨L,M,hL,hM⟩ := General.Compile.window_bounds hpack.smooth hR 0
  let V : ℝ → E n → E n := fun t => hamVF H (General.Compile.clamp01 t)
  have hV : ∀ t, LipschitzWith L (V t) := by
    intro t
    apply hL
    have hh := General.Compile.clamp01_mem t
    simpa only [Nat.cast_zero,zero_add,abs_of_nonneg hh.1] using hh.2
  have exists_curve : ∀ x : E n, ∃ y : ℝ → E n, y 0=x ∧ IsIntegralCurve y (hamVF H) :=
    fun x => General.Compile.exists_integralCurve_global hpack.smooth hR x
  choose y hy0 hy using exists_curve
  have hyv : ∀ x, IsIntegralCurveOn (y x) V (Icc 0 1) := by
    intro x t ht
    simpa only [V,General.Compile.clamp01_of_mem ht] using
      ((hy x).isIntegralCurveOn (Icc 0 1) t ht)
  have hstable : ∀ x z, dist (y x 1) (y z 1) ≤ dist x z*Real.exp L := by
    intro x z
    have hh := Effective.PackingCertificate.flow_error_with_initial hV (G:=V) (η:=0)
      (fun _ _ => by simp) (hyv z) (hyv x) (ρ:=dist x z)
      (by rw [hy0 x,hy0 z]) 1 (by norm_num)
    simpa only [gronwallBound_ε0,mul_one] using hh
  have hEnd : LipschitzWith ⟨Real.exp L,(Real.exp_pos _).le⟩ (fun x => y x 1) := by
    apply LipschitzWith.of_dist_le_mul
    intro x z
    change dist (y x 1) (y z 1) ≤ Real.exp L*dist x z
    simpa only [mul_comm] using hstable x z
  let f : E n → ℝ := fun x => Real.pi*‖y x 1‖^2
  have hf : Continuous f := continuous_const.mul (hEnd.continuous.norm.pow 2)
  let S : Set (E n) := ⋃ i : Fin k, capBall (s i) (c i)
  have hS : IsCompact S := isCompact_iUnion (fun i => compact_capBall (s i) (c i))
  by_cases hne : S.Nonempty
  · obtain ⟨x,hx,hmax⟩ := hS.exists_isMaxOn hne hf.continuousOn
    obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    have hxC : f x < C := by
      have hh := hpack.maps_into i x hi (y x) (hy0 x) ((hy x).isIntegralCurveOn (Icc 0 1))
      simpa only [capBallOpen,mem_setOf_eq,sub_zero,f] using hh
    have hfx : 0 ≤ f x := by dsimp [f]; positivity
    let C₀ : ℝ := (f x+C)/2
    have hC₀ : 0 < C₀ := by dsimp [C₀]; linarith
    have hC₀C : C₀ < C := by dsimp [C₀]; linarith
    refine ⟨C₀,hC₀,hC₀C,⟨hpack.smooth,hpack.compactSupport,hpack.exists_curve,?_⟩⟩
    intro j z hz γ hγ0 hγ
    have hγv : IsIntegralCurveOn γ V (Icc 0 1) := by
      intro t ht
      simpa only [V,General.Compile.clamp01_of_mem ht] using hγ t ht
    have hh := Effective.PackingCertificate.flow_error_with_initial hV (G:=V) (η:=0)
      (fun _ _ => by simp) (hyv z) hγv (ρ:=0)
      (by rw [hγ0,hy0 z,dist_self]) 1 (by norm_num)
    rw [gronwallBound_ε0_δ0] at hh
    have heq : γ 1=y z 1 := dist_le_zero.mp hh
    have hzS : z ∈ S := mem_iUnion.mpr ⟨j,hz⟩
    have hzmax : f z ≤ f x := hmax hzS
    change Real.pi*‖γ 1-0‖^2 < C₀
    rw [sub_zero,heq]
    change f z < C₀
    dsimp [C₀]
    linarith
  · refine ⟨C/2,by positivity,by linarith,⟨hpack.smooth,hpack.compactSupport,hpack.exists_curve,?_⟩⟩
    intro i x hx
    exact False.elim (hne ⟨x,mem_iUnion.mpr ⟨i,hx⟩⟩)

end SymplecticPacking.Problem
