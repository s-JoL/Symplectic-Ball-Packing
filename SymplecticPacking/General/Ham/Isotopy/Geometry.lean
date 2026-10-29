import SymplecticPacking.General.Ham.Isotopy.Smooth
import SymplecticPacking.General.Ham.Spec

/-!
# Symplecticity, injectivity, disjointness and boundedness of the common isotopy; conclusion

`IsoInput.commonIsotopy`: the explicit isotopy `isoF` satisfies `CommonIsotopy` with radii
`(r₁, r₂, r₃, r₄)` and ends at the maps `fᵢ`.
-/

noncomputable section

namespace SymplecticPacking.General.Ham.Isotopy

open Metric Set Filter Problem
open scoped ContDiff Topology Pointwise

variable {n k : ℕ} {f : Fin k → E n → E n} {s : Fin k → E n} {r1 r2 r3 r4 ρ : Fin k → ℝ}

lemma IsoInput.smul_mem_ball (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) {u : E n} (hu : u ∈ ball (0 : E n) (r4 i)) :
    c • u ∈ ball (0 : E n) (ρ i) := by
  obtain ⟨-, -, -, -, h4⟩ := hf.radii i
  rw [mem_ball_zero_iff]
  exact (norm_smul_le_of_mem_Icc hc u).trans_lt ((mem_ball_zero_iff.mp hu).trans h4)

/-- **Symplecticity.** -/
theorem IsoInput.isoF_sympl (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) (t : ℝ) {u : E n}
    (hu : u ∈ ball (0 : E n) (r4 i)) : IsSymplecticLinear (fderiv ℝ (isoF f s r3 i t) u) := by
  rcases slot_cases t with h | h | h | h
  · have : isoF f s r3 i t = fun u => pos f s r3 t i + u := funext (isoF_route' h i)
    rw [this, fderiv_const_add, fderiv_id']
    exact isSymplecticLinear_id
  · have : isoF f s r3 i t = fun u => farC f r3 i + linPath f i (clk 5 t) u :=
      funext (isoF_linear' h i)
    rw [this, fderiv_const_add, ContinuousLinearMap.fderiv]
    exact hf.linPath_sympl i _
  · have hs := hf.shapeParam_mem t
    have hsu := hf.smul_mem_ball i ⟨hs.1, hs.2.trans (by norm_num)⟩ hu
    have : isoF f s r3 i t = fun u => farC f r3 i + shape (f i) (tau f r3 * clk 6 t) u :=
      funext (isoF_shape' hf h i)
    rw [this, fderiv_const_add, (hasFDerivAt_shape (hf.smooth i) hsu).fderiv]
    exact hf.sympl i _ hsu
  · have hv := tailParam_mem (f := f) (r3 := r3) t
    have hv01 : tau f r3 + (1 - tau f r3) * clk 7 t ∈ Icc (0 : ℝ) 1 :=
      ⟨hf.tau_pos.le.trans hv.1, hv.2⟩
    have hvu := hf.smul_mem_ball i hv01 hu
    have hev : isoF f s r3 i t =ᶠ[𝓝 u] tailMap f i (tau f r3 + (1 - tau f r3) * clk 7 t) := by
      filter_upwards [isOpen_ball.mem_nhds hu] with w hw using isoF_tail' hf h i hw
    have hd : DifferentiableAt ℝ (f i) _ :=
      ((hf.smooth i).differentiableOn (by simp)).differentiableAt (isOpen_ball.mem_nhds hvu)
    have htail := hasFDerivAt_tail (ne_of_gt (hf.tau_pos.trans_le hv.1)) hd.hasFDerivAt
    rw [hev.fderiv_eq]
    rw [show tailMap f i (tau f r3 + (1 - tau f r3) * clk 7 t) =
      SymplecticPacking.tail (f i) (tau f r3 + (1 - tau f r3) * clk 7 t) from rfl,
      htail.fderiv]
    exact hf.sympl i _ hvu

/-- **Injectivity** on `B̄(r₃ᵢ)`. -/
theorem IsoInput.isoF_injOn (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) (t : ℝ) :
    InjOn (isoF f s r3 i t) (closedBall 0 (r3 i)) := by
  obtain ⟨-, -, -, h34, h4ρ⟩ := hf.radii i
  have hball : ∀ {u : E n}, u ∈ closedBall (0 : E n) (r3 i) → u ∈ ball (0 : E n) (r4 i) :=
    fun hu => mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hu).trans_lt h34)
  rcases slot_cases t with h | h | h | h
  · intro u _ w _ huw
    rw [isoF_route' h, isoF_route' h] at huw
    exact add_left_cancel huw
  · intro u _ w _ huw
    rw [isoF_linear' h, isoF_linear' h] at huw
    exact IsSymplecticLinear.injective (hf.linPath_sympl i _) (add_left_cancel huw)
  · intro u hu w hw huw
    rw [isoF_shape' hf h, isoF_shape' hf h] at huw
    have huw' := add_left_cancel huw
    set c := tau f r3 * clk 6 t
    have hs := hf.shapeParam_mem t
    by_cases hs0 : c = 0
    · rw [hs0, shape_zero, shape_zero] at huw'
      exact IsSymplecticLinear.injective (hf.lin_sympl i) huw'
    · have hs01 : c ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans (by norm_num)⟩
      rw [shape_eq (hf.smooth i) hs0 (hf.smul_mem_ball i hs01 (hball hu)),
        shape_eq (hf.smooth i) hs0 (hf.smul_mem_ball i hs01 (hball hw))] at huw'
      have h1 := smul_right_injective (E n) (inv_ne_zero hs0) huw'
      have h2 : f i (c • u) = f i (c • w) := sub_left_injective h1
      have hsu : ∀ {v : E n}, v ∈ closedBall (0 : E n) (r3 i) →
          c • v ∈ closedBall (0 : E n) (r4 i) :=
        fun hv => mem_closedBall_zero_iff.mpr
          ((norm_smul_le_of_mem_Icc hs01 _).trans ((mem_closedBall_zero_iff.mp hv).trans h34.le))
      exact smul_right_injective (E n) hs0 (hf.inj i (hsu hu) (hsu hw) h2)
  · have hv := tailParam_mem (f := f) (r3 := r3) t
    have hv0 : tau f r3 + (1 - tau f r3) * clk 7 t ≠ 0 :=
      ne_of_gt (hf.tau_pos.trans_le hv.1)
    have hsub : (tau f r3 + (1 - tau f r3) * clk 7 t) • closedBall (0 : E n) (r3 i) ⊆
        closedBall 0 (r4 i) :=
      (smul_closedBall_subset (hf.tau_pos.le.trans hv.1) hv.2).trans
        (closedBall_subset_closedBall h34.le)
    refine (tail_injOn (f i) hv0 hsub (hf.inj i)).congr fun u hu => ?_
    exact (isoF_tail' hf h i (hball hu)).symm

lemma disjoint_of_closedBall {A B : Set (E n)} {p q : E n} {a b : ℝ} (hA : A ⊆ closedBall p a)
    (hB : B ⊆ closedBall q b) (h : a + b < dist p q) : Disjoint A B :=
  (closedBall_disjoint_closedBall h).mono hA hB

/-- **Disjointness** of the images of the `B̄(r₃ᵢ)`. -/
theorem IsoInput.isoF_disj (hf : IsoInput f s r1 r2 r3 r4 ρ) (i j : Fin k) (t : ℝ)
    (hij : i ≠ j) :
    Disjoint (isoF f s r3 i t '' closedBall 0 (r3 i)) (isoF f s r3 j t '' closedBall 0 (r3 j)) := by
  have hL := hf.one_le_L
  have hr := hf.rsum_pos
  have hC := hf.farC_sep hij
  have h33 := hf.r3_add_r3_lt hij
  have hball : ∀ a, ∀ {u : E n}, u ∈ closedBall (0 : E n) (r3 a) → u ∈ ball (0 : E n) (r4 a) :=
    fun a u hu => mem_ball_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp hu).trans_lt (hf.radii a).2.2.2.1)
  rcases slot_cases t with h | h | h | h
  · have hsub : ∀ a, isoF f s r3 a t '' closedBall 0 (r3 a) ⊆ closedBall (pos f s r3 t a) (r3 a) := by
      rintro a _ ⟨u, hu, rfl⟩
      rw [isoF_route' h, mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      exact mem_closedBall_zero_iff.mp hu
    exact disjoint_of_closedBall (hsub i) (hsub j) (hf.pos_sep h hij)
  · have hsub : ∀ a, isoF f s r3 a t '' closedBall 0 (r3 a) ⊆
        closedBall (farC f r3 a) (bigL f r3) := by
      rintro a _ ⟨u, hu, rfl⟩
      rw [isoF_linear' h, mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      exact hf.norm_linPath_le a (clk_mem _ t) hu
    exact disjoint_of_closedBall (hsub i) (hsub j) (by nlinarith)
  · have hsub : ∀ a, isoF f s r3 a t '' closedBall 0 (r3 a) ⊆
        closedBall (farC f r3 a) (bigL f r3 * r3 a) := by
      rintro a _ ⟨u, hu, rfl⟩
      rw [isoF_shape' hf h, mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      have hs := hf.shapeParam_mem t
      have hs01 : tau f r3 * clk 6 t ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.trans (by norm_num)⟩
      have hb := norm_shape_le (f := f a) (R := r3 a) (L := bigL f r3)
        (fun y hy => hf.norm_fderiv_le a hy) (s := tau f r3 * clk 6 t) (u := u)
        ((norm_smul_le_of_mem_Icc hs01 u).trans (mem_closedBall_zero_iff.mp hu))
      exact hb.trans (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.mp hu) (by linarith))
    refine disjoint_of_closedBall (hsub i) (hsub j) ?_
    have : bigL f r3 * r3 i + bigL f r3 * r3 j < bigL f r3 * rsum r3 := by
      rw [← mul_add]; exact mul_lt_mul_of_pos_left h33 (by linarith)
    nlinarith
  · have hv := tailParam_mem (f := f) (r3 := r3) t
    set v := tau f r3 + (1 - tau f r3) * clk 7 t
    have hv0 : v ≠ 0 := ne_of_gt (hf.tau_pos.trans_le hv.1)
    have himg : ∀ a, isoF f s r3 a t '' closedBall 0 (r3 a) =
        v⁻¹ • (f a '' (v • closedBall (0 : E n) (r3 a))) := fun a => by
      rw [← SymplecticPacking.tail_image]
      exact image_congr fun u hu => isoF_tail' hf h a (hball a hu)
    have hsub : ∀ a, v • closedBall (0 : E n) (r3 a) ⊆ closedBall 0 (r4 a) := fun a =>
      (smul_closedBall_subset (hf.tau_pos.le.trans hv.1) hv.2).trans
        (closedBall_subset_closedBall (hf.radii a).2.2.2.1.le)
    rw [himg, himg, ← Set.image_smul, ← Set.image_smul]
    exact (Set.disjoint_image_iff (smul_right_injective (E n) (inv_ne_zero hv0))).mpr
      ((hf.disj i j hij).mono (image_mono (hsub i)) (image_mono (hsub j)))

/-- **Boundedness** on the `B̄(r₃ᵢ)`, uniformly in time. -/
theorem IsoInput.isoF_bounded (hf : IsoInput f s r1 r2 r3 r4 ρ) :
    ∃ S, ∀ i t, ∀ u ∈ closedBall (0 : E n) (r3 i), ‖isoF f s r3 i t u‖ ≤ S := by
  have hb : ∀ i, ∃ S, ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ closedBall (0 : E n) (r3 i),
      ‖isoF f s r3 i t u‖ ≤ S := by
    intro i
    have hK : IsCompact (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : E n) (r3 i)) :=
      isCompact_Icc.prod (isCompact_closedBall _ _)
    have hcont : ContinuousOn (fun p : ℝ × E n => isoF f s r3 i p.1 p.2)
        (Icc (0 : ℝ) 1 ×ˢ closedBall (0 : E n) (r3 i)) :=
      (hf.contDiffOn_isoF i).continuousOn.mono (prod_mono (subset_univ _)
        (closedBall_subset_ball (hf.radii i).2.2.2.1))
    obtain ⟨S, hS⟩ := hK.exists_bound_of_continuousOn hcont
    exact ⟨S, fun t ht u hu => hS (t, u) ⟨ht, hu⟩⟩
  choose S hS using hb
  refine ⟨∑ i, |S i|, fun i t u hu => ?_⟩
  have hle : |S i| ≤ ∑ j, |S j| :=
    Finset.single_le_sum (f := fun j => |S j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have key : ∀ t' ∈ Icc (0 : ℝ) 1, ‖isoF f s r3 i t' u‖ ≤ ∑ j, |S j| := fun t' ht' =>
    (hS i t' ht' u hu).trans ((le_abs_self _).trans hle)
  rcases le_or_gt t 0 with h0 | h0
  · rw [isoF_const_left i h0]; exact key 0 ⟨le_rfl, zero_le_one⟩
  · rcases le_or_gt 1 t with h1 | h1
    · rw [isoF_const_right i h1]; exact key 1 ⟨zero_le_one, le_rfl⟩
    · exact key t ⟨h0.le, h1.le⟩

/-- **Conclusion.** The explicit isotopy is a common isotopy with radii `(r₁, r₂, r₃, r₄)`,
starting at the translations `u ↦ sᵢ + u` and ending at the maps `fᵢ` on `B(r₄ᵢ)`. -/
theorem IsoInput.commonIsotopy (hf : IsoInput f s r1 r2 r3 r4 ρ) :
    CommonIsotopy (isoF f s r3) s r1 r2 r3 r4 ∧
      ∀ i, ∀ u ∈ ball (0 : E n) (r4 i), isoF f s r3 i 1 u = f i u := by
  refine ⟨⟨fun i => ?_, fun i => hf.contDiffOn_isoF i, fun i t u hu => hf.isoF_sympl i t hu,
    fun i t => hf.isoF_injOn i t, fun i j t hij => hf.isoF_disj i j t hij,
    fun i t ht => isoF_const_left i ht, fun i t ht => isoF_const_right i ht,
    fun i u => isoF_start i u, hf.isoF_bounded⟩, fun i u hu => hf.isoF_end i hu⟩
  obtain ⟨h1, h12, h23, h34, -⟩ := hf.radii i
  exact ⟨h1, h12, h23, h34⟩

end SymplecticPacking.General.Ham.Isotopy
