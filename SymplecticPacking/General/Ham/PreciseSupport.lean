import SymplecticPacking.General.Ham.TimeSupport

/-!
# The support of the Hamiltonian of a common isotopy

`isotopySupport F r₂` is the image of `[0,1] × B̄(r₂ i)` under the isotopies `F i`; it is
compact, and the Hamiltonian `ofIsotopy F r₁ r₂ r₃` vanishes outside it for all times.
-/

noncomputable section
namespace SymplecticPacking.General.Ham

open Set Metric Problem
variable {n k : ℕ}

def isotopySupport (F : Fin k → ℝ → E n → E n) (r2 : Fin k → ℝ) : Set (E n) :=
  ⋃ i,(fun p : ℝ × E n => F i p.1 p.2) '' (Icc (0 : ℝ) 1 ×ˢ closedBall 0 (r2 i))

theorem isotopySupport_compact {F : Fin k → ℝ → E n → E n} {s : Fin k → E n}
    {r1 r2 r3 ρ : Fin k → ℝ} (hF : CommonIsotopy F s r1 r2 r3 ρ) :
    IsCompact (isotopySupport F r2) := by
  apply isCompact_iUnion
  intro i
  apply (isCompact_Icc.prod (isCompact_closedBall (0 : E n) (r2 i))).image_of_continuousOn
  apply (hF.smooth i).continuousOn.mono
  rintro ⟨t,u⟩ ⟨_,hu⟩
  exact ⟨mem_univ _,(closedBall_subset_ball
    ((hF.radii i).2.2.1.trans (hF.radii i).2.2.2)) hu⟩

/-- The smaller cutoff balls, rather than the larger inverse domains, suffice
for the exact spatial support stated in the paper. -/
theorem ofIsotopy_support_precise {F : Fin k → ℝ → E n → E n} {s : Fin k → E n}
    {r1 r2 r3 ρ : Fin k → ℝ} (hF : CommonIsotopy F s r1 r2 r3 ρ) :
    ∀ t,∀ y ∉ isotopySupport F r2,ofIsotopy F r1 r2 r3 t y=0 := by
  intro t y hy
  by_cases ht : t ∈ Icc (0 : ℝ) 1
  · unfold ofIsotopy
    apply Finset.sum_eq_zero
    intro i _
    apply pushforward_eq_zero
    intro u hu hFu
    have hr : r2 i ≤ ‖u‖ := by
      by_contra h
      apply hy
      apply mem_iUnion.mpr
      exact ⟨i,(t,u),⟨ht,mem_closedBall_zero_iff.mpr (lt_of_not_ge h).le⟩,hFu⟩
    rw [radialCutoff_eq_zero (hF.radii i).2.1 (hF.radii i).1.le hr,zero_mul]
  · have ho : t ≤ 0 ∨ 1 ≤ t := by
      simp only [mem_Icc,not_and_or,not_le] at ht
      rcases ht with h|h
      · exact Or.inl h.le
      · exact Or.inr h.le
    exact ofIsotopy_eq_zero_of_time hF ho y

end SymplecticPacking.General.Ham
