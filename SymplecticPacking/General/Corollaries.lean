import SymplecticPacking.General.Main

/-!
# Equal-ball and unequal-cone corollaries

Equal-ball and four-dimensional unequal-cone consequences of the construction.
-/

noncomputable section
namespace SymplecticPacking.General
open Problem

theorem equal_admissible {n k : ℕ} {C c : ℝ} (hn : 2≤n) (hc : 0<c) (hC : 0<C)
    (hk : if n=2 then 9≤k else 2^n≤k) (hvol : (k:ℝ)*c^n<C^n) :
    Admissible n k C (fun _ => c) := by
  have hk1 : 1≤k := by
    by_cases h : n=2
    · have hh : 9≤k := by simpa only [if_pos h] using hk
      omega
    · have hh : 2^n≤k := by simpa only [if_neg h] using hk
      have hp : 0<(2:ℕ)^n := by positivity
      omega
  refine ⟨hn,hk1,hC,fun _ => hc,?_,?_,?_⟩
  · simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hvol
  · intro hn2 i
    have hk9 : 9≤k := by simpa only [if_pos hn2] using hk
    have h9r : (9:ℝ)≤k := by exact_mod_cast hk9
    have hv : (k:ℝ)*c^2<C^2 := hn2 ▸ hvol
    have hlo := mul_le_mul_of_nonneg_right h9r (sq_nonneg c)
    nlinarith [sq_nonneg (C-3*c)]
  · intro hn3 i j hij
    have hn2 : n≠2 := by omega
    have hkn : 2^n≤k := by simpa only [if_neg hn2] using hk
    have hknr : (2:ℝ)^n≤k := by exact_mod_cast hkn
    have hp : (2*c)^n<C^n := by
      rw [mul_pow]
      exact (mul_le_mul_of_nonneg_right hknr (pow_nonneg hc.le n)).trans_lt hvol
    have hlt : 2*c<C := by
      by_contra h
      have hh := pow_le_pow_left₀ hC.le (le_of_not_gt h) n
      exact (not_lt_of_ge hh) hp
    linarith

theorem equal_packing {n k : ℕ} {C c ε : ℝ} {s : Fin k → E n}
    (hn : 2≤n) (hc : 0<c) (hC : 0<C) (hε : ε<1)
    (hk : if n=2 then 9≤k else 2^n≤k) (hvol : (k:ℝ)*c^n<C^n)
    (hupper : C^n<(k:ℝ)*c^n/(1-ε)) (hs : BallsDisjoint n k (fun _ => c) s) :
    PackingSpec n k C (fun _ => c) s (packingHamiltonian n k C (fun _ => c) s) ∧
      1-ε<(k:ℝ)*c^n/C^n := by
  refine ⟨packing_main (equal_admissible hn hc hC hk hvol) hs,?_⟩
  have hh := (lt_div_iff₀ (by linarith : 0<1-ε)).mp hupper
  apply (lt_div_iff₀ (pow_pos hC n)).mpr
  nlinarith

def coneTarget {k : ℕ} (c : Fin k → ℝ) (ε : ℝ) : ℝ :=
  Real.sqrt ((∑ i,c i^2)/(1-ε/2))

theorem cone_admissible {k : ℕ} {c : Fin k → ℝ} {ε : ℝ}
    (hk : 1≤k) (hc : ∀ i,0<c i) (hε0 : 0<ε) (hε1 : ε<1)
    (hcone : ∀ i,c i≤Real.sqrt (∑ j,c j^2)/3) :
    Admissible 2 k (coneTarget c ε) c ∧
      (∑ i,c i^2)/(coneTarget c ε)^2=1-ε/2 := by
  let S : ℝ := ∑ i,c i^2
  have hS : 0<S := by
    let i : Fin k := ⟨0,by omega⟩
    have hh := Finset.single_le_sum (f:=fun j => c j^2)
      (fun j _ => sq_nonneg (c j)) (Finset.mem_univ i)
    exact (sq_pos_of_pos (hc i)).trans_le hh
  have hd : 0<1-ε/2 := by linarith
  have hv : S<S/(1-ε/2) := by
    apply (lt_div_iff₀ hd).mpr
    nlinarith
  have hC : 0<coneTarget c ε := Real.sqrt_pos.2 (div_pos hS hd)
  have hCsq : (coneTarget c ε)^2=S/(1-ε/2) :=
    Real.sq_sqrt (div_nonneg hS.le hd.le)
  have hroot : Real.sqrt S<coneTarget c ε :=
    Real.sqrt_lt_sqrt hS.le hv
  constructor
  · refine ⟨le_rfl,hk,hC,hc,?_,?_,?_⟩
    · change S<_
      rwa [hCsq]
    · intro _ i
      have hh := hcone i
      change c i≤Real.sqrt S/3 at hh
      linarith
    · intro h
      omega
  · rw [hCsq]
    change S/(S/(1-ε/2))=1-ε/2
    field_simp [hS.ne',hd.ne']

theorem unequal_cone_packing {k : ℕ} {c : Fin k → ℝ} {s : Fin k → E 2} {ε : ℝ}
    (hk : 1≤k) (hc : ∀ i,0<c i) (hε0 : 0<ε) (hε1 : ε<1)
    (hcone : ∀ i,c i≤Real.sqrt (∑ j,c j^2)/3) (hs : BallsDisjoint 2 k c s) :
    PackingSpec 2 k (coneTarget c ε) c s (packingHamiltonian 2 k (coneTarget c ε) c s) ∧
      (∑ i,c i^2)/(coneTarget c ε)^2=1-ε/2 := by
  obtain ⟨hA,hdensity⟩ := cone_admissible hk hc hε0 hε1 hcone
  exact ⟨packing_main hA hs,hdensity⟩

end SymplecticPacking.General
