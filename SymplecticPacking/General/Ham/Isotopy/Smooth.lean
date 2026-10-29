import SymplecticPacking.General.Ham.Isotopy.Slots

/-!
# Smoothness, constancy outside `[0,1]`, start and end of the common isotopy
-/

noncomputable section

namespace SymplecticPacking.General.Ham.Isotopy

open Metric Set Problem
open scoped ContDiff

variable {n k : ℕ} {f : Fin k → E n → E n} {s : Fin k → E n} {r1 r2 r3 r4 ρ : Fin k → ℝ}

lemma contDiff_routeClocks : ContDiff ℝ ∞ (routeClocks) := by
  rw [contDiff_pi]; intro l; exact contDiff_clk _

/-- **Smoothness** of `(t, u) ↦ F_{i,t}(u)` on `ℝ × B(r₄ᵢ)`. -/
theorem IsoInput.contDiffOn_isoF (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E n => isoF f s r3 i p.1 p.2) (univ ×ˢ ball (0 : E n) (r4 i)) := by
  obtain ⟨-, -, -, h34, h4ρ⟩ := hf.radii i
  have hr3 := hf.r3_pos i
  have hτ := hf.tau_pos
  have hτ1 : tau f r3 ≤ 1 / 2 := tau_le_half
  set ρa := (r4 i + ρ i) / 2
  have hρa0 : 0 ≤ ρa := by simp only [ρa]; linarith
  -- route term
  have hT1 : ContDiff ℝ ∞ (fun p : ℝ × E n =>
      routePos s (farC f r3) (routeConst s (farC f r3) r3) (routeClocks p.1) i + p.2) :=
    (((contDiff_routePos _ _ _ i).comp contDiff_routeClocks).comp contDiff_fst).add contDiff_snd
  -- linear term
  have hT2 : ContDiff ℝ ∞ (fun p : ℝ × E n => linPath f i (clk 5 p.1) p.2 - p.2) :=
    ((hf.contDiff_linPath_apply i).comp (((contDiff_clk _).comp contDiff_fst).prodMk
      contDiff_snd)).sub contDiff_snd
  -- shape term
  have hS := contDiffOn_shape (hf.smooth i) hρa0 (by simp only [ρa]; linarith)
  have hmaps : MapsTo (fun p : ℝ × E n => (tau f r3 * clk 6 p.1, p.2))
      (univ ×ˢ ball (0 : E n) (r4 i)) (Icc (-1) 1 ×ˢ ball (0 : E n) ρa) := by
    rintro ⟨t, u⟩ ⟨-, hu⟩
    have hc := clk_mem 6 t
    refine ⟨⟨by nlinarith [hc.1], by nlinarith [hc.2]⟩, ?_⟩
    exact mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hu).trans (by simp only [ρa]; linarith))
  have hT3 : ContDiffOn ℝ ∞ (fun p : ℝ × E n => shape (f i) (tau f r3 * clk 6 p.1) p.2 -
      lin f i p.2) (univ ×ˢ ball (0 : E n) (r4 i)) :=
    (hS.comp ((contDiff_const.mul ((contDiff_clk _).comp contDiff_fst)).prodMk
      contDiff_snd).contDiffOn hmaps).sub ((lin f i).contDiff.comp contDiff_snd).contDiffOn
  -- tail term
  set D : Set (ℝ × E n) := {q | 0 < q.1 ∧ q.1 • q.2 ∈ ball (0 : E n) (ρ i)}
  have hD : ContDiffOn ℝ ∞ (fun q : ℝ × E n => tailMap f i q.1 q.2) D := by
    unfold tailMap
    exact (contDiffOn_fst.inv fun q hq => hq.1.ne').smul
      ((hf.smooth i).comp (contDiff_fst.smul contDiff_snd).contDiffOn fun q hq => hq.2)
  have hv : ∀ t, tau f r3 + (1 - tau f r3) * clk 7 t ∈ Icc (tau f r3) 1 := fun t =>
    tailParam_mem t
  have hmapsT : ∀ g : ℝ → ℝ, (∀ t, g t ∈ Icc (tau f r3) 1) →
      MapsTo (fun p : ℝ × E n => (g p.1, p.2)) (univ ×ˢ ball (0 : E n) (r4 i)) D := by
    rintro g hg ⟨t, u⟩ ⟨-, hu⟩
    refine ⟨lt_of_lt_of_le hτ (hg t).1, ?_⟩
    rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg (hτ.le.trans (hg t).1)]
    calc g t * ‖u‖ ≤ 1 * ‖u‖ := by gcongr; exact (hg t).2
      _ < ρ i := by rw [one_mul]; exact (mem_ball_zero_iff.mp hu).trans h4ρ
  have hT4 : ContDiffOn ℝ ∞ (fun p : ℝ × E n =>
      tailMap f i (tau f r3 + (1 - tau f r3) * clk 7 p.1) p.2 -
        tailMap f i (tau f r3) p.2) (univ ×ˢ ball (0 : E n) (r4 i)) := by
    apply ContDiffOn.sub
    · exact hD.comp ((contDiff_const.add (contDiff_const.mul ((contDiff_clk _).comp
        contDiff_fst))).prodMk contDiff_snd).contDiffOn (hmapsT _ hv)
    · exact hD.comp (contDiff_const.prodMk contDiff_snd).contDiffOn
        (hmapsT (fun _ => tau f r3) fun _ => ⟨le_rfl, hτ1.trans (by norm_num)⟩)
  exact ((hT1.contDiffOn.add hT2.contDiffOn).add hT3).add hT4

/-! ### Ends of the isotopy -/

lemma isoF_eq_of_clocks {i : Fin k} {t t' : ℝ} (h : ∀ m, m ≤ 7 → clk m t = clk m t') :
    isoF f s r3 i t = isoF f s r3 i t' := by
  have hrc : routeClocks t = routeClocks t' := funext fun l => h l (by have := l.isLt; omega)
  funext u
  unfold isoF
  rw [hrc, h 5 (by omega), h 6 (by omega), h 7 le_rfl]

lemma isoF_const_left (i : Fin k) {t : ℝ} (ht : t ≤ 0) : isoF f s r3 i t = isoF f s r3 i 0 :=
  isoF_eq_of_clocks fun m _ => by rw [clk_of_nonpos ht, clk_of_nonpos le_rfl]

lemma isoF_const_right (i : Fin k) {t : ℝ} (ht : 1 ≤ t) : isoF f s r3 i t = isoF f s r3 i 1 :=
  isoF_eq_of_clocks fun m hm => by rw [clk_of_one_le hm ht, clk_of_one_le hm le_rfl]

/-- **Start**: `F_{i,0}(u) = sᵢ + u`. -/
lemma isoF_start (i : Fin k) (u : E n) : isoF f s r3 i 0 u = s i + u := by
  rw [isoF_route i (clk_of_nonpos le_rfl) (clk_of_nonpos le_rfl) (clk_of_nonpos le_rfl)]
  have : routeClocks 0 = fun _ => 0 := funext fun l => clk_of_nonpos le_rfl
  rw [this, routePos_zero]

/-- **End**: `F_{i,1}(u) = fᵢ(u)` on `B(r₄ᵢ)`. -/
lemma IsoInput.isoF_end (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) {u : E n}
    (hu : u ∈ ball (0 : E n) (r4 i)) : isoF f s r3 i 1 u = f i u := by
  rw [isoF_tail hf i (fun l => clk_of_one_le (by have := l.isLt; omega) le_rfl)
    (clk_of_one_le (by omega) le_rfl) (clk_of_one_le (by omega) le_rfl) hu,
    clk_of_one_le le_rfl le_rfl]
  simp [tailMap]

end SymplecticPacking.General.Ham.Isotopy
