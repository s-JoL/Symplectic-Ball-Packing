import SymplecticPacking.HighDim.Handle.QuadricTightFiniteAtlas
import OAI.Geometry.BallPacking.SurfaceArea.QuadricSmoothExhaustion

/-!
# Connectedness of the trimmed finite quadric nerve

Every retained inner box meets the connected compact base, so its finite nerve is connected.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped Topology

theorem radial_projection_near {q : ℂ} {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 < δ)
    (hq : ‖q‖ < R+δ) : ∃ u : ℂ, ‖u‖ ≤ R ∧ ‖u-q‖ < δ := by
  by_cases hinside : ‖q‖ ≤ R
  · exact ⟨q,hinside,by simpa using hδ⟩
  · have hqn : 0 < ‖q‖ := lt_of_le_of_lt hR (lt_of_not_ge hinside)
    let u : ℂ := (R/‖q‖) • q
    have hscale : 0 ≤ R/‖q‖ := div_nonneg hR hqn.le
    have hunit : (R/‖q‖)*‖q‖ = R := div_mul_cancel₀ _ hqn.ne'
    have hu : ‖u‖ = R := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hscale]
      exact hunit
    have hd : ‖u-q‖ = ‖q‖-R := by
      have he : u-q = (R/‖q‖-1) • q := by dsimp [u]; push_cast; ring
      rw [he,norm_smul,Real.norm_eq_abs,
        abs_of_nonpos (sub_nonpos.mpr ((div_le_one hqn).mpr (le_of_not_ge hinside)))]
      nlinarith
    exact ⟨u,hu.le,by rw [hd]; linarith⟩

theorem ordinaryRawBox_inner_meets {m : ℕ} {a : Fin m → ℂ}
    (c : locus a) (hc : ∀ j, c.val.2 j ≠ 0) {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hm : ∀ j, (2*r)*(2*‖c.val.1‖+2*r) < ‖c.val.2 j‖^2)
    (hnear : ‖c.val.1‖ < R+r/16) :
    ((ordinaryRawBox c hc r hr hm).innerOpen ∩ projectionDomain a R).Nonempty := by
  obtain ⟨u,hu,hdu⟩ := radial_projection_near hR (show 0<r/16 by linarith) hnear
  have hut : u ∈ (ordinaryExplicitChart c hc).target :=
    ordinaryLocalTarget_closedBall c hc hm (by
      rw [Metric.mem_closedBall,dist_eq_norm]
      exact hdu.le.trans (by linarith))
  let x := (ordinaryExplicitChart c hc).symm u
  have hx : x ∈ (ordinaryRealExplicitChart c hc).source :=
    ⟨(ordinaryExplicitChart c hc).map_target hut,mem_univ _⟩
  have hcoord : ordinaryRealExplicitChart c hc x = Complex.equivRealProdCLM u :=
    congrArg Complex.equivRealProdCLM ((ordinaryExplicitChart c hc).right_inv hut)
  refine ⟨x,⟨hx,?_⟩,?_⟩
  · change ordinaryRealExplicitChart c hc x ∈ Metric.ball (Complex.equivRealProdCLM c.val.1) (r/4)
    rw [hcoord,Metric.mem_ball,dist_eq_norm,← map_sub]
    exact (Complex.equivRealProd_apply_le (u-c.val.1)).trans_lt (hdu.trans (by linarith))
  · exact hu

theorem quadricTightFiniteBox_inner_meets {m : ℕ} (a : Fin m → ℚ)
    [Fact (Injective (fun j => (a j:ℂ)))] [Fact (∀ j, (a j:ℂ) ≠ 0)]
    {R : ℚ} (hR : 0 < R) (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖)
    (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (hbranch : ∀ i, ‖(a i:ℂ)‖ < (R:ℝ)^2)
    (idx : QuadricTightFiniteIndex a R) :
    ((quadricTightFiniteBox a hR.le hsep₀ hsep idx).innerOpen ∩
      projectionDomain (fun j => (a j:ℂ)) R).Nonempty := by
  have hR' : 0 < (R:ℝ) := by exact_mod_cast hR
  cases idx with
  | inl i =>
    let q := rationalGridPoint (quadricGridSize R) (quadricGridMesh R) i.val.1.val
    let c := ordinaryPresentationCenter (fun j => (a j:ℂ)) i.val.2 (rationalComplex q)
    have hv := (rationalOrdinaryValid_sound a hR.le q i.val.1.property i.val.2).1
    have hc := QuadricBoxCode.ordinary_margin_regular _ hv.1 hv.2
    have hfilter : ‖rationalComplex q‖^2 < ((R:ℝ)+(quadricGridRadius R:ℝ)/16)^2 := by
      have hh := (Rat.cast_lt (K := ℝ)).mpr i.property
      rw [rationalNormSq_cast] at hh
      push_cast at hh
      exact hh
    have hr : 0 < (quadricGridRadius R:ℝ) := by exact_mod_cast quadricGridRadius_pos hR.le
    apply ordinaryRawBox_inner_meets c hc hr hR'.le hv.2
    change ‖rationalComplex q‖ < (R:ℝ)+(quadricGridRadius R:ℝ)/16
    nlinarith [norm_nonneg (rationalComplex q)]
  | inr idx =>
    let c := branchPresentationCenter (fun j => (a j:ℂ)) idx.1 idx.2.1 idx.2.2
    have hc := branchPresentationCenter_regular (fun j => (a j:ℂ)) Fact.out Fact.out
      idx.1 idx.2.1 idx.2.2
    have hs : c ∈ (branchRealExplicitChart c idx.1 hc).source :=
      ⟨branchExplicitChart_center c idx.1 hc,mem_univ _⟩
    refine ⟨c,⟨hs,?_⟩,?_⟩
    · change Complex.equivRealProdCLM (c.val.2 idx.1) ∈
        Metric.ball (Complex.equivRealProdCLM (c.val.2 idx.1)) ((1/8:ℝ)/4)
      exact Metric.mem_ball_self (by norm_num)
    · change ‖signedRoot idx.2.1 (a idx.1:ℂ)‖ ≤ (R:ℝ)
      nlinarith [norm_signedRoot_sq idx.2.1 (a idx.1:ℂ), hbranch idx.1,
        norm_nonneg (signedRoot idx.2.1 (a idx.1:ℂ))]

/-- A relative open cover of a preconnected set has a connected overlap nerve if every
retained set meets that set. This needs no finite-subcover or connectedness oracle. -/
theorem openCover_overlap_chain {M I : Type} [TopologicalSpace M]
    (O : I → Set M) {K : Set M} (hK : IsPreconnected K) (hO : ∀ i, IsOpen (O i))
    (hcover : K ⊆ ⋃ i, O i) (hmeet : ∀ i, (K ∩ O i).Nonempty) (i j : I) :
    Relation.TransGen (fun a b => (O a ∩ O b).Nonempty) i j := by
  classical
  by_contra hij
  let S : Set I := {k | Relation.TransGen (fun a b => (O a ∩ O b).Nonempty) i k}
  let U : Set M := ⋃ k ∈ S, O k
  let V : Set M := ⋃ k ∈ Sᶜ, O k
  obtain ⟨a,haK,haO⟩ := hmeet i
  obtain ⟨b,hbK,hbO⟩ := hmeet j
  have hiS : i ∈ S := Relation.TransGen.single ⟨a,haO,haO⟩
  have hsplit : K ⊆ U ∪ V := by
    intro x hx
    obtain ⟨k,hkx⟩ := mem_iUnion.mp (hcover hx)
    by_cases hk : k ∈ S
    · exact Or.inl (mem_iUnion₂_of_mem hk hkx)
    · exact Or.inr (mem_iUnion₂_of_mem hk hkx)
  obtain ⟨x,hxK,hxU,hxV⟩ := hK U V (isOpen_biUnion fun k _ => hO k)
    (isOpen_biUnion fun k _ => hO k) hsplit
    ⟨a,haK,mem_iUnion₂_of_mem hiS haO⟩
    ⟨b,hbK,mem_iUnion₂_of_mem hij hbO⟩
  obtain ⟨k,hk,hxk⟩ := mem_iUnion₂.mp hxU
  obtain ⟨l,hl,hxl⟩ := mem_iUnion₂.mp hxV
  exact hl (hk.tail ⟨x,hxk,hxl⟩)

theorem quadricTightFiniteBox_nerve_connected {m : ℕ} (a : Fin m → ℚ)
    [Fact (Injective (fun j => (a j:ℂ)))] [Fact (∀ j, (a j:ℂ) ≠ 0)]
    {R : ℚ} (hR : 0 < R) (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖)
    (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (hbranch : ∀ i, ‖(a i:ℂ)‖ < (R:ℝ)^2)
    (i j : QuadricTightFiniteIndex a R) :
    Relation.TransGen (fun c d =>
      ((quadricTightFiniteBox a hR.le hsep₀ hsep c).innerOpen ∩
       (quadricTightFiniteBox a hR.le hsep₀ hsep d).innerOpen).Nonempty) i j := by
  have hR' : 0 < (R:ℝ) := by exact_mod_cast hR
  have hcl : closure (interior (projectionDomain (fun j => (a j:ℂ)) R)) =
      projectionDomain (fun j => (a j:ℂ)) R := by
    rw [projectionDomain_interior hR',
      ← (curveProjection_open (a := fun j => (a j:ℂ))).preimage_closure_eq_closure_preimage
        (curveProjection_continuous (fun j => (a j:ℂ))), closure_ball (0:ℂ) hR'.ne']
    ext x
    simp [projectionDomain,curveProjection,Metric.mem_closedBall,dist_zero_right]
  have hK : IsPreconnected (projectionDomain (fun j => (a j:ℂ)) R) := by
    rw [← hcl]
    exact (projectionDomain_interior_connected hR' hbranch).isPreconnected.closure
  apply openCover_overlap_chain _ hK (fun c => (quadricTightFiniteBox a hR.le hsep₀ hsep c).innerOpen_open)
  · intro x hx
    obtain ⟨idx,hi⟩ := quadricTightFiniteBox_cover a hR.le hsep₀ hsep x hx
    exact mem_iUnion.mpr ⟨idx,hi⟩
  · intro idx
    obtain ⟨x,hxB,hxK⟩ := quadricTightFiniteBox_inner_meets a hR hsep₀ hsep hbranch idx
    exact ⟨x,hxK,hxB⟩

end SymplecticPacking.HighDim.ToricPackingStages
