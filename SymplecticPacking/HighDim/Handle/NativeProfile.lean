import SymplecticPacking.HighDim.Comparator.Datum
import SymplecticPacking.BranchLarge3.NegPolySpec

/-!
# Native comparator profile

Finite polyhedral comparator input, independent of any manifold model.
-/

noncomputable section
namespace SymplecticPacking.HighDim.NativeProfile
open Set MeasureTheory
open OAI.PackingSufficiencySupport.MomentPolytope
open SymplecticPacking.BranchLarge3.Surf
open scoped Pointwise
variable {m q k : ℕ}

def mean (Δ : Polytope m q) (A : Moments m → ℝ) (r : Fin k → ℝ) : ℝ :=
  (∫ p in Δ.set,A p-∑ i,max (r i-∑ j,p j) 0)/(volume Δ.set).toReal

def tolerance (Δ : Polytope m q) (A : Moments m → ℝ) (r : Fin k → ℝ) (d₀ : ℝ) : ℝ :=
  min d₀ (mean Δ A r)/32

def input (Δ : Polytope m q) (negP : PolyFn m) (τ d₀ : ℝ) : CmpInput m q where
  Δ := Δ
  P p := -PolyFn.eval negP p
  τ := τ
  β := d₀/2
  d := min (((∫ p in Δ.set,-PolyFn.eval negP p)/(volume Δ.set).toReal)/2) (d₀/4)

theorem input_spec (Δ : Polytope m q) (hΔ : Δ.Spec) (negP : PolyFn m) (τ d₀ : ℝ)
    (hτ : 0<τ) (hτ1 : τ<1) (hd₀ : 0 < d₀)
    (hout : ∀ p∈Δ.set,p∉τ • Δ.set → d₀/2 ≤ -PolyFn.eval negP p)
    (hint : 0<∫ p in Δ.set,-PolyFn.eval negP p) : (input Δ negP τ d₀).Spec := by
  have hvol : 0 < (volume Δ.set).toReal := by
    refine ENNReal.toReal_pos ?_ hΔ.compact.measure_lt_top.ne
    intro h0
    rw [Measure.restrict_eq_zero.mpr h0,integral_zero_measure] at hint
    linarith
  let I := input Δ negP τ d₀
  have hm : 0 < I.mean := div_pos hint hvol
  refine ⟨hΔ,(PolyFn.eval_continuous _).neg.continuousOn,?_,hvol,hτ,hτ1,?_,?_,?_,?_⟩
  · exact (PolyFn.eval_convexOn negP).neg.subset (subset_univ _) (Polytope.convex_set _)
  · intro p hp hpd
    apply hout p hp
    rintro ⟨w,hw,rfl⟩
    apply hpd
    refine ⟨fun j => ?_,fun ν => ?_⟩
    · simpa only [Pi.smul_apply,smul_eq_mul] using mul_nonneg hτ.le (hw.1 j)
    · change (∑ j,Δ.b ν j*(τ*w j)) ≤ τ*Δ.ℓ ν
      have he : (∑ j,Δ.b ν j*(τ*w j))=τ*∑ j,Δ.b ν j*w j := by
        rw [Finset.mul_sum];exact Finset.sum_congr rfl fun j _ => by ring
      rw [he]
      exact mul_le_mul_of_nonneg_left (hw.2 ν) hτ.le
  · exact lt_min (by change 0 < I.mean/2;positivity) (by positivity)
  · exact (min_le_left _ _).trans_lt (by change I.mean/2 < I.mean;linarith)
  · exact (min_le_right _ _).trans_lt (by change d₀/4 < d₀/2;linarith)

theorem tolerance_spec (Δ : Polytope m q) (hΔ : Δ.Spec) (A : Moments m → ℝ)
    (hA : ContinuousOn A Δ.set) (r : Fin k → ℝ) (FA : PolyFn m) (hFA : FA≠[])
    (hAF : ∀ p∈Δ.set,A p= -PolyFn.eval FA p)
    (hmean : 0<∫ p in Δ.set,A p-∑ i,max (r i-∑ j,p j) 0)
    {τ d₀ : ℝ} (hd₀ : 0 < d₀)
    (houter : ∀ p∈Δ.set,p∉τ • Δ.set → d₀ ≤ A p-∑ i,max (r i-∑ j,p j) 0) :
    let e := tolerance Δ A r d₀
    0 < e ∧ negPolyOf FA r e≠[] ∧
      (∀ p∈Δ.set,-PolyFn.eval (negPolyOf FA r e) p ≤ A p-∑ i,max (r i-∑ j,p j) 0-e) ∧
      (∀ p∈Δ.set,p∉τ • Δ.set → d₀/2 ≤ -PolyFn.eval (negPolyOf FA r e) p) ∧
      0<∫ p in Δ.set,-PolyFn.eval (negPolyOf FA r e) p := by
  intro e
  have hvol : 0 < (volume Δ.set).toReal := by
    refine ENNReal.toReal_pos ?_ hΔ.compact.measure_lt_top.ne
    intro h0
    rw [Measure.restrict_eq_zero.mpr h0,integral_zero_measure] at hmean
    linarith
  have hm : 0 < mean Δ A r := div_pos hmean hvol
  have he : 0 < e := div_pos (lt_min hd₀ hm) (by norm_num)
  have he₀ : e ≤ d₀/32 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hem : e ≤ mean Δ A r/32 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  have hcm : mean Δ A r*(volume Δ.set).toReal=∫ p in Δ.set,A p-∑ i,max (r i-∑ j,p j) 0 :=
    div_mul_cancel₀ _ hvol.ne'
  have hbudget : 4*e*(volume Δ.set).toReal ≤ ∫ p in Δ.set,A p-∑ i,max (r i-∑ j,p j) 0 := by
    have hh := mul_le_mul_of_nonneg_right hem hvol.le
    nlinarith
  exact ⟨he,negPolyOf_spec Δ.b Δ.ℓ hΔ.compact A hA r FA hFA hAF hmean houter he (by linarith) hbudget⟩

end SymplecticPacking.HighDim.NativeProfile
