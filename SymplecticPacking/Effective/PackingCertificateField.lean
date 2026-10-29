import SymplecticPacking.Effective.PackingCertificatePolynomial
import SymplecticPacking.Effective.PackingCertificate
import Mathlib.Analysis.ODE.ExistUnique

/-!
# Bounded clipped polynomial fields

Bounded clipped polynomial fields: all quantitative constants are finite program data.
-/

noncomputable section
namespace SymplecticPacking.Effective.PackingPolynomial
open Set
open scoped ContDiff NNReal Topology
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def clip (a b x : ℝ) : ℝ := max a (min x b)

theorem clip_lipschitz (a b : ℝ) : LipschitzWith 1 (clip a b) :=
  (LipschitzWith.id.min_const b).const_max a

theorem clip_mem {a b : ℝ} (hab : a≤b) (x : ℝ) : clip a b x ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

theorem clip_eq {a b x : ℝ} (hx : x∈Icc a b) : clip a b x=x := by
  simp [clip, min_eq_left hx.2, max_eq_right hx.1]

/-- The time coordinate and spatial coordinates are all clamped by rational
min/max operations. The spatial cutoff plateau has radius `B/2`. -/
def clippedPoint (d B : ℕ) (t : ℝ) (x : Fin d → ℝ) : Fin (d+1) → ℝ :=
  Fin.cons (clip 0 1 t) (fun j => clip (-(B:ℝ)/2) ((B:ℝ)/2) (x j))

theorem clippedPoint_bound (d B : ℕ) (hB : 1≤B) (t : ℝ) (x : Fin d → ℝ) :
    ∀ j, |clippedPoint d B t x j| ≤ (B:ℝ) := by
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · have hh := clip_mem zero_le_one t
    have hB' : (1:ℝ)≤B := by exact_mod_cast hB
    simpa only [clippedPoint, Fin.cons_zero, abs_of_nonneg hh.1] using hh.2.trans hB'
  · have hh := clip_mem (show -(B:ℝ)/2≤(B:ℝ)/2 by
      nlinarith [(Nat.cast_nonneg B : (0:ℝ)≤B)]) (x j)
    change |clip (-(B:ℝ)/2) ((B:ℝ)/2) (x j)| ≤ (B:ℝ)
    exact abs_le.mpr ⟨by linarith [hh.1], by linarith [hh.2]⟩

theorem clippedPoint_space (d B : ℕ) (t : ℝ) (x y : Fin d → ℝ) :
    ‖clippedPoint d B t x-clippedPoint d B t y‖ ≤ ‖x-y‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [clippedPoint]
  · have hc := (clip_lipschitz (-(B:ℝ)/2) ((B:ℝ)/2)).dist_le_mul (x j) (y j)
    have hx := norm_le_pi_norm (x-y) j
    simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hc
    have hx' : |x j-y j|≤‖x-y‖ := by simpa only [Pi.sub_apply, Real.norm_eq_abs] using hx
    simpa only [clippedPoint, Fin.cons_succ, Pi.sub_apply, Real.norm_eq_abs] using hc.trans hx'

theorem clippedPoint_time (d B : ℕ) (s t : ℝ) (x : Fin d → ℝ) :
    ‖clippedPoint d B t x-clippedPoint d B s x‖ ≤ |t-s| := by
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa only [clippedPoint, Fin.cons_zero, Pi.sub_apply, Real.norm_eq_abs,
      Real.dist_eq, NNReal.coe_one, one_mul] using (clip_lipschitz 0 1).dist_le_mul t s
  · simp [clippedPoint]

def field (n B : ℕ) (e : Expr) (t : ℝ) (x : Fin (2*n) → ℝ) : Fin (2*n) → ℝ :=
  fun i => if h : i.val<n then
    realEval (2*n+1) (derivative (i.val+n+1) e) (clippedPoint (2*n) B t x)
  else -realEval (2*n+1) (derivative (i.val-n+1) e) (clippedPoint (2*n) B t x)

theorem field_speed (n B : ℕ) (e : Expr) (hB : 1≤B) (t : ℝ) (x : Fin (2*n) → ℝ) :
    ‖field n B e t x‖ ≤ (budget B e:ℝ) := by
  apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)).mpr
  intro i
  have hd : ∀ j, |realEval (2*n+1) (derivative j e) (clippedPoint (2*n) B t x)| ≤
      (budget B e:ℝ) := fun j => (eval_bound _ _ _ (clippedPoint_bound _ _ hB _ _)).trans
        (by exact_mod_cast (budget_bounds B e).2.2 j |>.1)
  simp only [field, Real.norm_eq_abs]
  split_ifs <;> simpa only [abs_neg] using hd _

theorem field_space (n B : ℕ) (e : Expr) (hB : 1≤B) (t : ℝ)
    (x y : Fin (2*n) → ℝ) :
    ‖field n B e t x-field n B e t y‖ ≤ (budget B e:ℝ)*‖x-y‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))).mpr
  intro i
  have hd : ∀ j, |realEval (2*n+1) (derivative j e) (clippedPoint (2*n) B t x)-
      realEval (2*n+1) (derivative j e) (clippedPoint (2*n) B t y)| ≤
      (budget B e:ℝ)*‖x-y‖ := by
    intro j
    refine (eval_lipschitz _ _ _ (clippedPoint_bound _ _ hB _ _)
      (clippedPoint_bound _ _ hB _ _)).trans ?_
    exact mul_le_mul (by exact_mod_cast (budget_bounds B e).2.2 j |>.2)
      (clippedPoint_space _ _ _ _ _) (norm_nonneg _) (Nat.cast_nonneg _)
  simp only [field, Pi.sub_apply, Real.norm_eq_abs]
  split_ifs <;> first | exact hd _ | simpa only [neg_sub_neg, abs_sub_comm] using hd _

theorem field_time (n B : ℕ) (e : Expr) (hB : 1≤B) (s t : ℝ)
    (x : Fin (2*n) → ℝ) :
    ‖field n B e t x-field n B e s x‖ ≤ (budget B e:ℝ)*|t-s| := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))).mpr
  intro i
  have hd : ∀ j, |realEval (2*n+1) (derivative j e) (clippedPoint (2*n) B t x)-
      realEval (2*n+1) (derivative j e) (clippedPoint (2*n) B s x)| ≤
      (budget B e:ℝ)*|t-s| := by
    intro j
    refine (eval_lipschitz _ _ _ (clippedPoint_bound _ _ hB _ _)
      (clippedPoint_bound _ _ hB _ _)).trans ?_
    exact mul_le_mul (by exact_mod_cast (budget_bounds B e).2.2 j |>.2)
      (clippedPoint_time _ _ _ _ _) (norm_nonneg _) (Nat.cast_nonneg _)
  simp only [field, Pi.sub_apply, Real.norm_eq_abs]
  split_ifs <;> first | exact hd _ | simpa only [neg_sub_neg, abs_sub_comm] using hd _

theorem field_lipschitz (n B : ℕ) (e : Expr) (hB : 1≤B) (t : ℝ) :
    LipschitzWith (budget B e:ℝ≥0) (field n B e t) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [dist_eq_norm, NNReal.coe_natCast] using field_space n B e hB t x y

theorem field_time_lipschitz (n B : ℕ) (e : Expr) (hB : 1≤B)
    (x : Fin (2*n) → ℝ) :
    LipschitzWith (budget B e:ℝ≥0) (fun t => field n B e t x) :=
  LipschitzWith.of_dist_le_mul fun t s => by
    simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_natCast] using
      field_time n B e hB s t x

/-- The clipped field has a genuine solution for every initial value. The
proof uses only the finite coefficient budget, not a supplied solution oracle. -/
theorem exists_curve_bounds (n B : ℕ) (e : Expr) (hB : 1≤B)
    (x : Fin (2*n) → ℝ) :
    ∃ γ : ℝ → Fin (2*n) → ℝ, γ 0=x ∧
      ODE.Bounds (field n B e) γ (budget B e:ℝ) (budget B e:ℝ) (budget B e:ℝ) := by
  let K : ℝ≥0 := budget B e
  have hPL : IsPicardLindelof (field n B e) (tmin := (-1:ℝ)) (tmax := 2)
      ⟨0, by norm_num⟩ x (K*2) 0 K K := by
    refine ⟨fun t _ => (field_lipschitz n B e hB t).lipschitzOnWith,
      fun y _ => (field_time_lipschitz n B e hB y).continuous.continuousOn,
      fun t _ y _ => field_speed n B e hB t y, ?_⟩
    norm_num
  obtain ⟨γ, hγ0, hγ⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  refine ⟨γ, hγ0, ?_⟩
  refine ⟨Nat.cast_nonneg _, Nat.cast_nonneg _, Nat.cast_nonneg _, ?_,
    fun t _ => field_speed n B e hB t (γ t),
    fun s _ t _ y => field_time n B e hB s t y,
    fun t _ y z => field_space n B e hB t y z⟩
  intro t ht
  exact (hγ t ⟨by linarith [ht.1], by linarith [ht.2]⟩).hasDerivAt
    (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))

end SymplecticPacking.Effective.PackingPolynomial
