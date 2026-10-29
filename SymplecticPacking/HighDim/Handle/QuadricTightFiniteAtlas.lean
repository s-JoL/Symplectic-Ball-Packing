import SymplecticPacking.HighDim.Handle.QuadricFiniteAtlas

/-!
# The trimmed finite quadric atlas

The finite grid trimmed so that every retained inner box meets the covered compact base.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.DiagonalQuadrics

abbrev QuadricTightOrdinaryIndex {m : ℕ} (a : Fin m → ℚ) (R : ℚ) :=
  {idx : OrdinaryGridIndex a R (quadricGridRadius R) quadricGridThreshold
    (quadricGridSize R) (quadricGridMesh R) //
    rationalNormSq (rationalGridPoint (quadricGridSize R) (quadricGridMesh R) idx.1.val) <
      (R+quadricGridRadius R/16)^2}

abbrev QuadricTightFiniteIndex {m : ℕ} (a : Fin m → ℚ) (R : ℚ) :=
  QuadricTightOrdinaryIndex a R ⊕ (Fin m × Bool × (Fin m → Bool))

variable {m : ℕ} (a : Fin m → ℚ)
  [Fact (Injective (fun j => (a j:ℂ)))] [Fact (∀ j, (a j:ℂ) ≠ 0)]

def quadricTightFiniteBox {R : ℚ} (hR : 0 ≤ R) (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖)
    (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (idx : QuadricTightFiniteIndex a R) : RawCoordinateBox (locus (fun j => (a j:ℂ))) :=
  match idx with
  | .inl i => ordinaryGridBox a hR i.val
  | .inr (i, ε₀, ε) => uniformBranchBox a hsep₀ hsep i ε₀ ε

theorem tightOrdinaryGridBox_cover {R : ℚ} (hR : 0 ≤ R)
    (x : locus (fun j => (a j:ℂ))) (hxR : ‖x.val.1‖ ≤ R)
    (hxη : ∀ j, (quadricGridThreshold:ℝ) ≤ ‖x.val.2 j‖) :
    ∃ idx : QuadricTightOrdinaryIndex a R,
      x ∈ (ordinaryGridBox a hR idx.val).innerOpen := by
  let r := quadricGridRadius R
  let h := quadricGridMesh R
  let N := quadricGridSize R
  have hr : 0 < r := quadricGridRadius_pos hR
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  have hh : 0 < (h:ℝ) := by exact_mod_cast quadricGridMesh_pos hR
  have hN : (R:ℝ)+h < (N:ℝ)*h := by exact_mod_cast quadricGridSize_bound hR
  obtain ⟨i, hi⟩ := rationalGridPoint_cover N h hh hN x.val.1 hxR
  let q := rationalGridPoint N h i
  have hmesh : 2*(h:ℝ) = (r:ℝ)/16 := by
    dsimp [h,r,quadricGridMesh]
    push_cast
    ring
  have hq : rationalComplex q ∈ Metric.closedBall x.val.1 ((r:ℝ)/8) := by
    rw [Metric.mem_closedBall,dist_eq_norm]
    exact hi.le.trans (by rw [hmesh]; linarith)
  have hqnorm : ‖rationalComplex q‖ < (R:ℝ)+(r:ℝ)/16 := by
    calc
      ‖rationalComplex q‖ = ‖(rationalComplex q-x.val.1)+x.val.1‖ := by congr 1; abel
      _ ≤ ‖rationalComplex q-x.val.1‖+‖x.val.1‖ := norm_add_le _ _
      _ < 2*(h:ℝ)+(R:ℝ) := add_lt_add_of_lt_of_le hi hxR
      _ = (R:ℝ)+(r:ℝ)/16 := by rw [hmesh]; ring
  have hfilter : rationalNormSq q < (R+r/16)^2 := by
    have hhreal : (rationalNormSq q:ℝ) < ((R+r/16:ℚ):ℝ)^2 := by
      rw [rationalNormSq_cast]
      push_cast
      have hR' : 0 ≤ (R:ℝ) := by exact_mod_cast hR
      nlinarith [norm_nonneg (rationalComplex q)]
    exact_mod_cast hhreal
  have hval := rationalOrdinaryValid_of_grid a hR hr
    ((quadricGridRadius_bound hR).trans (by norm_num))
    (by norm_num [quadricGridThreshold]) (quadricGrid_budget hR) (quadricGrid_small hR)
    x hxR hxη q hq
  have hsmall : 4*(r:ℝ)*(2*(R:ℝ)+4*r) < (quadricGridThreshold:ℝ)^2 := by
    exact_mod_cast quadricGrid_small hR
  obtain ⟨ε,hc,hm,hin⟩ := ordinary_grid_box_cover x hxR
    (by norm_num [quadricGridThreshold]) hr' hxη (rationalComplex q) hq hsmall
  exact ⟨⟨(⟨i,hval⟩,ε),hfilter⟩,hin⟩

theorem quadricTightFiniteBox_cover {R : ℚ} (hR : 0 ≤ R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (x : locus (fun j => (a j:ℂ))) (hxR : ‖x.val.1‖ ≤ R) :
    ∃ idx : QuadricTightFiniteIndex a R,
      x ∈ (quadricTightFiniteBox a hR hsep₀ hsep idx).innerOpen := by
  by_cases hx : ∀ j, (quadricGridThreshold:ℝ) ≤ ‖x.val.2 j‖
  · obtain ⟨i,hi⟩ := tightOrdinaryGridBox_cover a hR x hxR hx
    exact ⟨.inl i,hi⟩
  · push Not at hx
    obtain ⟨i,hi⟩ := hx
    have hxi : ‖x.val.2 i‖ ≤ (1/8:ℝ)/8 := by
      norm_num [quadricGridThreshold] at hi ⊢
      exact hi.le
    obtain ⟨ε₀,ε,hm₀,hm,hin⟩ := branch_grid_box_cover Fact.out Fact.out x i
      (by norm_num : (0:ℝ)<1) (by norm_num : (0:ℝ)<1/8)
      (hsep₀ i) (hsep i) (by norm_num : 4*(1/8:ℝ)^2<1) hxi
    exact ⟨.inr (i,ε₀,ε),hin⟩

#check_explicit quadricTightFiniteBox
end SymplecticPacking.HighDim.ToricPackingStages
