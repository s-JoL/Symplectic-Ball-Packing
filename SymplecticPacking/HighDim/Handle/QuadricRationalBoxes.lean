import SymplecticPacking.HighDim.Handle.QuadricRationalAtlas

/-!
# Rational coordinate boxes on the quadric

Coverage by coordinate boxes with rational code data.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Filter
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped Topology

theorem exists_positive_rat_of_nhds {p : ℝ → Prop} (hp : ∀ᶠ r in 𝓝 0, p r) :
    ∃ r : ℚ, 0 < (r : ℝ) ∧ p r := by
  obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.mp hp
  obtain ⟨r, hr, hrδ⟩ := exists_rat_btwn hδ
  refine ⟨r, hr, hP ?_⟩
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos hr] using hrδ

theorem exists_positive_rat_root_margin {I : Type} [Finite I] (t : ℂ) (F : I → ℝ)
    (hF : ∀ i, 0 < F i) :
    ∃ r : ℚ, 0 < (r : ℝ) ∧ ∀ i, (2*(r:ℝ))*(2*‖t‖+2*r) < F i := by
  apply exists_positive_rat_of_nhds (p := fun r : ℝ => ∀ i, (2*r)*(2*‖t‖+2*r) < F i)
  apply Filter.eventually_all.mpr
  intro i
  have hc : Continuous (fun r : ℝ => (2*r)*(2*‖t‖+2*r)) := by fun_prop
  have h0 : (2*(0:ℝ))*(2*‖t‖+2*0) < F i := by simpa using hF i
  exact (isOpen_lt hc continuous_const).mem_nhds h0

def ordinaryBoxMargin {m : ℕ} {a : Fin m → ℂ} (r : ℝ) (c : locus a) : Prop :=
  ∀ j, (2*r)*(2*‖c.val.1‖+2*r) < ‖c.val.2 j‖^2

theorem ordinaryBoxMargin_open {m : ℕ} {a : Fin m → ℂ} (r : ℝ) :
    IsOpen {c : locus a | ordinaryBoxMargin r c} := by
  simp only [ordinaryBoxMargin, ofPred_forall]
  exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) (by fun_prop)

/-- Every ordinary point is in an inner box whose centre coordinate and radius are rational.
The remaining centre data are just the finite root signs. -/
theorem ordinary_rational_boxes_cover {m : ℕ} {a : Fin m → ℂ} (x : locus a)
    (hx : ∀ j, x.val.2 j ≠ 0) :
    ∃ q : ℚ × ℚ, ∃ ε : Fin m → Bool, ∃ r : ℚ,
      let c := ordinaryPresentationCenter a ε (rationalComplex q)
      ∃ hc : ∀ j, c.val.2 j ≠ 0, ∃ hr : 0 < (r : ℝ),
      ∃ hm : ordinaryBoxMargin r c, x ∈ (ordinaryRawBox c hc r hr hm).innerOpen := by
  obtain ⟨r, hr, hmargin⟩ := exists_positive_rat_root_margin x.val.1
    (fun j : Fin m => ‖x.val.2 j‖^2) (fun j => pow_pos (norm_pos_iff.mpr (hx j)) 2)
  let C := ordinaryLocalLift x hx
  have hxT : x.val.1 ∈ ordinaryLocalTarget x := by intro j; simp
  have hC : C x.val.1 = x := ordinaryLocalLift_left x hx (ordinaryExplicitChart_center x hx)
  have hcont : ContinuousAt C x.val.1 := (ordinaryExplicitChart x hx).continuousAt_symm hxT
  have hS : {c | ordinaryCentreCondition x c} ∈ 𝓝 (C x.val.1) := by
    rw [hC]
    exact (ordinaryCentreCondition_open x).mem_nhds (ordinaryCentreCondition_self x hx)
  have hM : {c | ordinaryBoxMargin r c} ∈ 𝓝 (C x.val.1) := by
    rw [hC]
    exact (ordinaryBoxMargin_open r).mem_nhds hmargin
  have hB : Metric.ball x.val.1 ((r:ℝ)/8) ∈ 𝓝 x.val.1 :=
    Metric.ball_mem_nhds _ (by positivity)
  have hN := Filter.inter_mem (hcont.preimage_mem_nhds hS)
    (Filter.inter_mem (hcont.preimage_mem_nhds hM) hB)
  obtain ⟨q, hqS, hqM, hqB⟩ := rationalComplex_dense.mem_nhds hN
  let c := C (rationalComplex q)
  have hc : ∀ j, c.val.2 j ≠ 0 := hqS.1
  have hin : x ∈ (ordinaryRawBox c hc r hr hqM).innerOpen := by
    have hs : x ∈ (ordinaryRealExplicitChart c hc).source := ⟨hqS.2, Set.mem_univ _⟩
    refine ⟨hs, ?_⟩
    change Complex.equivRealProdCLM x.val.1 ∈
      Metric.ball (Complex.equivRealProdCLM (rationalComplex q)) ((r:ℝ)/4)
    rw [Metric.mem_ball, dist_eq_norm, ← map_sub]
    have hd : ‖x.val.1-rationalComplex q‖ < (r:ℝ)/8 := by
      simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hqB
    exact (Complex.equivRealProd_apply_le _).trans_lt (by linarith)

  obtain ⟨ε, hε⟩ := ordinaryPresentationCenter_complete a c
  have hc0 : c.val.1 = rationalComplex q := rfl
  rw [hc0] at hε
  refine ⟨q, ε, r, ?_⟩
  change ∃ hc' hr' hm', x ∈ (ordinaryRawBox _ hc' r hr' hm').innerOpen
  rw [hε]
  exact ⟨hc, hr, hqM, hin⟩

theorem branch_centre_rational_box {m : ℕ} {a : Fin m → ℂ} (x : locus a) (i : Fin m)
    (hx : x.val ∈ regularCoordinate (some i)) :
    ∃ r : ℚ, ∃ hr : 0 < (r : ℝ),
    ∃ hm₀ : (2*(r:ℝ))*(2*‖x.val.2 i‖+2*r) < ‖x.val.1‖^2,
    ∃ hm : ∀ j, j≠i → (2*(r:ℝ))*(2*‖x.val.2 i‖+2*r) < ‖x.val.2 j‖^2,
      x ∈ (branchRawBox x i hx r hr hm₀ hm).innerOpen := by
  let F : Option (Fin m) → ℝ
    | none => ‖x.val.1‖^2
    | some j => if j=i then ‖x.val.1‖^2 else ‖x.val.2 j‖^2
  have hF : ∀ j, 0 < F j := by
    intro j
    cases j with
    | none => exact pow_pos (norm_pos_iff.mpr hx.1) 2
    | some j =>
      by_cases hji : j=i
      · simp only [F, ite_eq_left hji]
        exact pow_pos (norm_pos_iff.mpr hx.1) 2
      · simp only [F, ite_eq_right hji]
        exact pow_pos (norm_pos_iff.mpr (hx.2 j hji)) 2
  obtain ⟨r, hr, hm⟩ := exists_positive_rat_root_margin (x.val.2 i) F hF
  have hm₀ : (2*(r:ℝ))*(2*‖x.val.2 i‖+2*r) < ‖x.val.1‖^2 := hm none
  have hmj : ∀ j, j≠i → (2*(r:ℝ))*(2*‖x.val.2 i‖+2*r) < ‖x.val.2 j‖^2 := by
    intro j hji
    simpa only [F, ite_eq_right hji] using hm (some j)
  refine ⟨r, hr, hm₀, hmj, ?_, ?_⟩
  · exact ⟨branchExplicitChart_center x i hx, Set.mem_univ _⟩
  · exact Metric.mem_ball_self (by positivity)

end SymplecticPacking.HighDim.ToricPackingStages
