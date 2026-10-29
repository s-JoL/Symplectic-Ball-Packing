import SymplecticPacking.BranchLarge3.InnerNativeSpec

/-!
# The six-dimensional inner packing

The six-dimensional inner packing, evaluated by the native finite-atlas construction.
-/

noncomputable section
namespace SymplecticPacking.BranchLarge3
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.MomentPolytope
open OAI.PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set

structure ChainHyp {N : ℕ} (r r' : Fin N → ℝ) (a : ℚ) : Prop where
  ne : 0 < N
  r_pos : ∀ i, 0 < r i
  r'_nonneg : ∀ i, 0 ≤ r' i
  r'_lt : ∀ i, r' i < r i
  a_gt : (1 : ℚ) / 2 < a
  a_lt : a < 1
  r_lt : ∀ i, r i < 1 - (a : ℝ)
  vol : ∑ i, r i ^ 3 < 1 - (a : ℝ) ^ 3

theorem ChainHyp.comparison {N : ℕ} {r r' : Fin N → ℝ} {a : ℚ} (h : ChainHyp r r' a) : CmpHyp r a := by
  have ha : (1:ℝ)/2 < (a:ℝ) := by
    have hh : (((1:ℚ)/2:ℚ):ℝ) < (a:ℝ) := Rat.cast_lt.mpr h.a_gt
    norm_num at hh ⊢
    exact hh
  exact ⟨h.ne,h.r_pos,ha,by exact_mod_cast h.a_lt,h.r_lt,h.vol⟩

/-- The weighted physical model used by the inner maps. -/
def innerW {N : ℕ} (Q : ℕ) (r : Fin N → ℝ) (a : ℚ) : Weights := NativeInner.weights Q r a

/-- The common certified level includes both the area and collar moduli. -/
def innerLevel {N : ℕ} (Q : ℕ) (r _r' : Fin N → ℝ) (a : ℚ) : ℕ := NativeInner.level Q r a

/-- Three native inverse flows applied to the native layer map. -/
def innerMaps {N : ℕ} (Q : ℕ) (r r' : Fin N → ℝ) (a : ℚ) :
    Fin N → Ambient 3 → BaseCurve × PlanePhase (Fin 2) := NativeInner.maps Q r r' a

lemma cmp_rat {N : ℕ} {r r' : Fin N → ℝ} {a : ℚ} (h : ChainHyp r r' a) :
    0 < (cmpData r a).e ∧ (cmpData r a).e < 1 - a ∧ 1 - a < (cmpData r a).d₂ ∧
      (cmpData r a).d₂ < (2 - a) / 3 ∧ (cmpData r a).h₁ < (cmpData r a).h₂ := by
  have ha : (1 : ℝ) / 2 < (a : ℝ) := by
    have hh : (((1 : ℚ) / 2 : ℚ) : ℝ) < (a : ℝ) := Rat.cast_lt.mpr h.a_gt
    norm_num at hh ⊢; exact hh
  have ha1 : (a : ℝ) < 1 := by exact_mod_cast h.a_lt
  obtain ⟨_, hhe, hes, hsd, hdh, hhd, hd₂, hh₁, -⟩ :=
    cmpData_spec (r := r) (a := a) ⟨h.ne, h.r_pos, ha, ha1, h.r_lt, h.vol⟩
  have hhe' : ((cmpData r a).h₁ : ℝ) < (cmpData r a).e := by exact_mod_cast hhe
  have hdh' : ((cmpData r a).d₁ : ℝ) < (cmpData r a).h₂ := by exact_mod_cast hdh
  have hhd' : ((cmpData r a).h₂ : ℝ) < (cmpData r a).d₂ := by exact_mod_cast hhd
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have : (0 : ℝ) < (cmpData r a).e := by linarith
    exact_mod_cast this
  · have : ((cmpData r a).e : ℝ) < ((1 - a : ℚ) : ℝ) := by push_cast; exact hes
    exact_mod_cast this
  · have : ((1 - a : ℚ) : ℝ) < (cmpData r a).d₂ := by push_cast; linarith
    exact_mod_cast this
  · have : ((cmpData r a).d₂ : ℝ) < (((2 - a) / 3 : ℚ) : ℝ) := by push_cast; exact hd₂
    exact_mod_cast this
  · have : ((cmpData r a).h₁ : ℝ) < (cmpData r a).h₂ := by linarith
    exact_mod_cast this

/-- The numerical part of S3: the weights satisfy the OpenAI inequalities. -/
theorem innerW_spec {N : ℕ} (Q : ℕ) {r r' : Fin N → ℝ} {a : ℚ} (h : ChainHyp r r' a) :
    let W := innerW Q r a
    Q < W.L ∧ 0 < W.L ∧ 0 < W.A ∧ 0 < W.S ∧ W.A < W.S ∧ W.A ≤ W.B ∧ W.S ≤ W.B ∧
      3 * W.B < W.D ∧ 3 * W.S < W.D ∧
      (W.A : ℝ) = (W.L : ℝ) * ((cmpData r a).e : ℝ) ∧
      (W.B : ℝ) = (W.L : ℝ) * ((cmpData r a).d₂ : ℝ) ∧
      (W.D : ℝ) = (W.L : ℝ) * (2 - (a : ℝ)) ∧ (W.S : ℝ) = (W.L : ℝ) * (1 - (a : ℝ)) := by
  obtain ⟨he0, hes, hsd, hd₂, -⟩ := cmp_rat h
  exact weights_spec Q h.a_gt h.a_lt he0 hes hsd hd₂

/-- The native inner maps have the physical packing properties. -/
theorem inner_spec {N : ℕ} (Q : ℕ) {r r' : Fin N → ℝ} {a : ℚ} (h : ChainHyp r r' a) :
    let W := innerW Q r a
    let φ := innerMaps Q r r' a
    (∀ i, r i < (cmpData r a).h₁) ∧ (cmpData r a).h₁ < (cmpData r a).h₂ ∧
      ((cmpData r a).h₁ : ℝ) < (W.A : ℝ) / W.L ∧ ((cmpData r a).h₂ : ℝ) < (W.B : ℝ) / W.L ∧
      (∀ i, FormNeighborhoodEmbedding (closedBall 3 (r' i)) (fun _ => successorStandardForm 2)
        (globalHorizontalCoupling phaseArea
          (physicalPrimitive (A := W.A) (B := W.B) W.D W.S (1 / ((W.L : ℝ) * Real.pi)) W.L ∘
            planeMoments)) (φ i)) ∧
      (∀ i, MapsTo (φ i) (closedBall 3 (r' i))
        (interior (cubicExhaustion (innerLevel Q r r' a) ×ˢ planeRegion sixModelBounds
          ![((cmpData r a).h₁ : ℝ), (cmpData r a).h₂]))) ∧
      Pairwise (fun i j => Disjoint (φ i '' closedBall 3 (r' i)) (φ j '' closedBall 3 (r' j))) := by
  intro W φ
  have hCmp := h.comparison
  obtain ⟨hrh,hhe,_,_,_,hhd,_,_,_,_,_,_,_,_,_,_⟩ := cmpData_spec hCmp
  obtain ⟨_,hL,_,_,_,_,_,_,_,heA,heB,_,_⟩ := innerW_spec Q h
  obtain ⟨_,_,_,_,hh₁₂⟩ := cmp_rat h
  have hLr : 0<(W.L:ℝ) := Nat.cast_pos.mpr hL
  obtain ⟨hf,hm,hd⟩ := NativeInner.spec Q hCmp h.r'_nonneg h.r'_lt
  refine ⟨hrh,hh₁₂,?_,?_,?_,?_,?_⟩
  · rw [heA,mul_div_cancel_left₀ _ hLr.ne']
    exact Rat.cast_lt.mpr hhe
  · rw [heB,mul_div_cancel_left₀ _ hLr.ne']
    exact Rat.cast_lt.mpr hhd
  · simpa only [φ,W,innerMaps,innerW,NativeInner.coefficient] using hf
  · simpa only [φ,innerMaps,innerLevel] using hm
  · simpa only [φ,innerMaps] using hd

#check_explicit innerMaps
end SymplecticPacking.BranchLarge3
