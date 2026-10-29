import SymplecticPacking.HighDim.Handle.QuadricGridCover

/-!
# Branch boxes on the diagonal quadric

Uniform branch boxes from a quantitative separation bound for the branch parameters.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.DiagonalQuadrics

theorem norm_sq_lower_of_sq_eq {z b v : ℂ} (hz : z^2 = b+v^2) :
    ‖b‖-‖v‖^2 ≤ ‖z‖^2 := by
  have he : b = z^2-v^2 := by rw [hz]; ring
  have hn : ‖b‖ ≤ ‖z‖^2+‖v‖^2 := by
    rw [he]
    exact (norm_sub_le _ _).trans_eq (by rw [norm_pow, norm_pow])
  linarith

/-- A nearby root determines one of the two finite signs with positive ratio. -/
theorem root_sign_positive_ratio {z b v : ℂ} (hz : z^2 = b+v^2)
    (hv : 2*‖v‖^2 < ‖b‖) : ∃ ε : Bool, 0 < (z/signedRoot ε b).re := by
  have hlow := norm_sq_lower_of_sq_eq hz
  have hz₀ : z ≠ 0 := by
    intro hh
    rw [hh, norm_zero, zero_pow (by decide)] at hlow
    nlinarith [sq_nonneg ‖v‖]
  have hd : 0 < (1+(-v^2)/z^2 : ℂ).re := by
    apply rootArgument_re_pos hz₀
    rw [norm_neg, norm_pow]
    linarith
  have hs : rootNear z (-v^2)^2 = b := by
    rw [rootNear_sq hz₀, hz]
    ring
  obtain ⟨ε, hε⟩ := signedRoot_complete hs
  refine ⟨ε, ?_⟩
  rw [hε]
  exact div_rootNear_re_pos hz₀ hd

theorem norm_signedRoot_sq (ε : Bool) (b : ℂ) : ‖signedRoot ε b‖^2 = ‖b‖ := by
  rw [← norm_pow, signedRoot_sq]

/-- A single fixed branch radius works for all root signs as soon as the parameter
separation is bounded below. -/
theorem branch_grid_box_cover {m : ℕ} {a : Fin m → ℂ} (ha : Injective a)
    (ha₀ : ∀ j, a j ≠ 0) (x : locus a) (i : Fin m) {L r : ℝ}
    (hL : 0 < L) (hr : 0 < r) (hsep₀ : L ≤ ‖a i‖)
    (hsep : ∀ j, j≠i → L ≤ ‖a i-a j‖) (hsmall : 4*r^2 < L)
    (hxi : ‖x.val.2 i‖ ≤ r/8) :
    ∃ ε₀ : Bool, ∃ ε : Fin m → Bool,
      let c := branchPresentationCenter a i ε₀ ε
      ∃ hm₀ : (2*r)*(2*‖c.val.2 i‖+2*r) < ‖c.val.1‖^2,
      ∃ hm : ∀ j, j≠i → (2*r)*(2*‖c.val.2 i‖+2*r) < ‖c.val.2 j‖^2,
        x ∈ (branchRawBox c i (branchPresentationCenter_regular a ha ha₀ i ε₀ ε)
          r hr hm₀ hm).innerOpen := by
  have hv : 2*‖x.val.2 i‖^2 < L := by
    nlinarith [norm_nonneg (x.val.2 i)]
  have hx₀ : x.val.1^2 = a i+(x.val.2 i)^2 := by
    have hh := mem_locus.mp x.property i
    linear_combination -hh
  obtain ⟨ε₀, hε₀⟩ := root_sign_positive_ratio hx₀ (hv.trans_le hsep₀)
  have hh (j : Fin m) : ∃ ε : Bool, j≠i → 0 < (x.val.2 j/signedRoot ε (a i-a j)).re := by
    by_cases hji : j=i
    · exact ⟨false, fun hn => (hn hji).elim⟩
    · have hxj : (x.val.2 j)^2 = (a i-a j)+(x.val.2 i)^2 := by
        rw [mem_locus.mp x.property j, hx₀]
        ring
      obtain ⟨ε, hε⟩ := root_sign_positive_ratio hxj (hv.trans_le (hsep j hji))
      exact ⟨ε, fun _ => hε⟩
  choose ε hε using hh
  let c := branchPresentationCenter a i ε₀ ε
  have hc := branchPresentationCenter_regular a ha ha₀ i ε₀ ε
  have hci : c.val.2 i = 0 := by simp only [c, branchPresentationCenter, ite_true]
  have hnorm₀ : L ≤ ‖c.val.1‖^2 := (norm_signedRoot_sq ε₀ (a i)) ▸ hsep₀
  have hnorm (j : Fin m) (hji : j≠i) : L ≤ ‖c.val.2 j‖^2 := by
    change L ≤ ‖if j=i then 0 else signedRoot (ε j) (a i-a j)‖^2
    rw [ite_eq_right hji, norm_signedRoot_sq]
    exact hsep j hji
  have hm₀ : (2*r)*(2*‖c.val.2 i‖+2*r) < ‖c.val.1‖^2 := by
    rw [hci, norm_zero]
    nlinarith
  have hm : ∀ j, j≠i → (2*r)*(2*‖c.val.2 i‖+2*r) < ‖c.val.2 j‖^2 := by
    intro j hji
    rw [hci, norm_zero]
    nlinarith [hnorm j hji]
  refine ⟨ε₀, ε, hm₀, hm, ?_⟩
  have hsource : x ∈ branchLocalSource c i := by
    refine ⟨⟨?_, ?_⟩, hε₀, ?_⟩
    · change 0 < (1+((x.val.2 i)^2-(c.val.2 i)^2)/c.val.1^2 : ℂ).re
      rw [hci, zero_pow (by decide), sub_zero]
      apply rootArgument_re_pos hc.1
      rw [norm_pow]
      linarith
    · intro j hji
      change 0 < (1+((x.val.2 i)^2-(c.val.2 i)^2)/(c.val.2 j)^2 : ℂ).re
      rw [hci, zero_pow (by decide), sub_zero]
      apply rootArgument_re_pos (hc.2 j hji)
      rw [norm_pow]
      linarith [hnorm j hji]
    · intro j hji
      change 0 < (x.val.2 j/(if j=i then 0 else signedRoot (ε j) (a i-a j))).re
      rw [ite_eq_right hji]
      exact hε j hji
  refine ⟨⟨hsource, Set.mem_univ _⟩, ?_⟩
  change Complex.equivRealProdCLM (x.val.2 i) ∈
    Metric.ball (Complex.equivRealProdCLM (c.val.2 i)) (r/4)
  rw [hci, map_zero, Metric.mem_ball, dist_zero_right]
  exact (Complex.equivRealProd_apply_le _).trans_lt (by linarith)

end SymplecticPacking.HighDim.ToricPackingStages
