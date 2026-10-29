import SymplecticPacking.General.CompileExistence

/-!
# Flow error and trajectory tubes of the compilation

All-time compilation error and compact trajectory tubes for finite certificates.
-/

noncomputable section
namespace SymplecticPacking.General.Compile
open Metric Set Filter Problem
open scoped ContDiff Topology NNReal

private theorem flow_error_le_at {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {v w : ℝ → X → X} {L : ℝ≥0} (hL : (L:ℝ)≠0) {η : ℝ}
    (hv : ∀ t,LipschitzWith L (v t)) (hη : ∀ t x,dist (w t x) (v t x)≤η)
    {y z : ℝ → X} (hy : IsIntegralCurveOn y v (Icc 0 1))
    (hz : IsIntegralCurveOn z w (Icc 0 1)) (h0 : z 0=y 0) (t : ℝ) (ht : t∈Icc 0 1) :
    dist (z t) (y t)≤η*(Real.exp L-1)/L := by
  have hIci : ∀ s∈Ico (0:ℝ) 1,Icc (0:ℝ) 1∈nhdsWithin s (Ici s) := fun s hs =>
    Filter.mem_of_superset (Icc_mem_nhdsGE hs.2) (Icc_subset_Icc hs.1 le_rfl)
  have key := dist_le_of_approx_trajectories_ODE (v:=v) (K:=L) (δ:=0)
    (εf:=η) (εg:=0) (f:=z) (g:=y) (f':=fun s => w s (z s))
    (g':=fun s => v s (y s)) hv
    (fun s hs => (hz s hs).continuousWithinAt)
    (fun s hs => (hz s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (hIci s hs))
    (fun s _ => hη s (z s))
    (fun s hs => (hy s hs).continuousWithinAt)
    (fun s hs => (hy s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin (hIci s hs))
    (fun s _ => by rw [dist_self]) (by rw [h0,dist_self]) t ht
  rw [gronwallBound_of_K_ne_0 hL] at key
  simp only [zero_mul,zero_add,add_zero,sub_zero] at key
  have hη0 : 0≤η := (dist_nonneg (x:=w 0 0) (y:=v 0 0)).trans (hη 0 0)
  have he : Real.exp ((L:ℝ)*t)≤Real.exp L := Real.exp_le_exp.mpr
    (by nlinarith [L.coe_nonneg,ht.2])
  calc dist (z t) (y t)≤η/L*(Real.exp ((L:ℝ)*t)-1) := key
       _ ≤ η/L*(Real.exp L-1) := mul_le_mul_of_nonneg_left
          (sub_le_sub_right he 1) (div_nonneg hη0 L.coe_nonneg)
       _ = η*(Real.exp L-1)/L := by ring

/-- Compilation controls the entire closed time interval, including both endpoints. -/
theorem flow_error_at {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    {H : ℝ → E n → ℝ} (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2))
    (D : CompilationDatum n k C c s H)
    {γ y : ℝ → E n} (hγ : IsIntegralCurveOn γ (Problem.hamVF D.Hfin) (Icc 0 1))
    (hy : IsIntegralCurveOn y (Problem.hamVF H) (Icc 0 1)) (h0 : γ 0=y 0)
    (t : ℝ) (ht : t∈Icc 0 1) : dist (γ t) (y t)<D.bR := by
  have hLX1 : 1≤D.LX := by
    have hh := D.LX_ge 0 (by norm_num) 0
    linarith [norm_nonneg (fderiv ℝ (fderiv ℝ (H 0)) 0)]
  have hδ : (0:ℝ)<D.δ := by exact_mod_cast D.δ_pos
  have hbR : (0:ℝ)<D.bR := by exact_mod_cast D.bR_pos
  have hCβ : (1:ℝ)≤D.Cβ := by
    have hh := D.Cβ_ge 0
    linarith [norm_nonneg (fderiv ℝ (boxCut n D.B) (0:E n))]
  let L : ℝ≥0 := ⟨D.LX,by linarith⟩
  let v := fun r => Problem.hamVF H (clamp01 r)
  let w := fun r => Problem.hamVF D.Hfin (clamp01 r)
  have hv : ∀ r,LipschitzWith L (v r) := fun r =>
    hamVF_lipschitz hH (D.LX_ge _ (clamp01_mem r)) (by linarith)
  have hη : ∀ r x,dist (w r x) (v r x)≤D.η := by
    intro r x
    rw [dist_eq_norm]
    refine (field_error hH D (clamp01_mem r) x).trans ?_
    have hh := D.δ_lt
    rw [lt_div_iff₀ (by linarith : 0<16*(1+D.Cβ))] at hh
    unfold CompilationDatum.η
    nlinarith
  have hγ' : IsIntegralCurveOn γ w (Icc 0 1) := fun r hr => by
    simp only [w,clamp01_of_mem hr]
    exact hγ r hr
  have hy' : IsIntegralCurveOn y v (Icc 0 1) := fun r hr => by
    simp only [v,clamp01_of_mem hr]
    exact hy r hr
  have hh := flow_error_le_at (L:=L) (by change D.LX≠0; linarith) hv hη hy' hγ' h0 t ht
  exact hh.trans_lt (SymplecticPacking.eta_choice hLX1 hbR)

/-- A smooth spatially supported field cannot move a trajectory beyond both the initial
radius and its support radius. The uniqueness comparison is based at the final time. -/
theorem norm_le_max_of_support {n : ℕ} {H : ℝ → E n → ℝ}
    (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2)) {R : ℝ}
    (hR : ∀ r z,R<‖z‖ → H r z=0) {y : ℝ → E n}
    (hy : IsIntegralCurveOn y (Problem.hamVF H) (Icc 0 1)) (t : ℝ) (ht : t∈Icc 0 1) :
    ‖y t‖≤ max ‖y 0‖ R := by
  by_contra hn
  have hout : R<‖y t‖ := (le_max_right _ _).trans_lt (lt_of_not_ge hn)
  obtain ⟨K,_,hK,_⟩ := window_bounds hH hR 0
  have hsub : Icc (0:ℝ) t⊆Icc (0:ℝ) 1 := Icc_subset_Icc le_rfl ht.2
  have hc : ContinuousOn y (Icc (0:ℝ) 1) := fun r hr => (hy r hr).continuousWithinAt
  have hIic : ∀ r∈Ioc (0:ℝ) t,Icc (0:ℝ) 1∈nhdsWithin r (Iic r) := by
    intro r hr
    exact Filter.mem_of_superset (Icc_mem_nhdsLE hr.1)
      (Icc_subset_Icc le_rfl (hr.2.trans ht.2))
  have heq : EqOn y (fun _ => y t) (Icc (0:ℝ) t) :=
    ODE_solution_unique_of_mem_Icc_left (K:=K) (v:=Problem.hamVF H) (s:=fun _ => univ)
      (fun r hr => (hK r (by rw [abs_of_nonneg hr.1.le]; linarith [hr.2,ht.2])).lipschitzOnWith)
      (hc.mono hsub)
      (fun r hr => (hy r ⟨hr.1.le,hr.2.trans ht.2⟩).mono_of_mem_nhdsWithin (hIic r hr))
      (fun _ _ => mem_univ _) continuous_const.continuousOn
      (fun r _ => by
        rw [hamVF_eq_zero_of_norm hR hout]
        exact hasDerivWithinAt_const r (Iic r) (y t))
      (fun _ _ => mem_univ _) rfl
  have hz := heq ⟨le_rfl,ht.1⟩
  have hstrict : ‖y 0‖<‖y t‖ := (le_max_left _ _).trans_lt (lt_of_not_ge hn)
  exact (ne_of_lt hstrict) (congrArg norm hz)

/-- A coarse support radius suffices; the larger plateau in `CompileExistence` absorbs it. -/
theorem source_norm_bound {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    {H : ℝ → E n → ℝ} (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2))
    (D : CompilationDatum n k C c s H) {y : ℝ → E n}
    (hy : IsIntegralCurveOn y (Problem.hamVF H) (Icc 0 1)) (t : ℝ) (ht : t∈Icc 0 1) :
    ‖y t‖≤ max ‖y 0‖ (2*n*(D.Sbox:ℝ)) := by
  apply norm_le_max_of_support hH ?_ hy t ht
  exact support_of_coords (by exact_mod_cast D.Sbox_pos.le) D.support

/-- The compiled trajectory has a controlled compact tube on the whole closed interval. -/
theorem compiled_norm_lt {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    {H : ℝ → E n → ℝ} (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2))
    (D : CompilationDatum n k C c s H)
    {γ y : ℝ → E n} (hγ : IsIntegralCurveOn γ (Problem.hamVF D.Hfin) (Icc 0 1))
    (hy : IsIntegralCurveOn y (Problem.hamVF H) (Icc 0 1)) (h0 : γ 0=y 0)
    (t : ℝ) (ht : t∈Icc 0 1) :
    ‖γ t‖<(D.bR:ℝ)+max ‖y 0‖ (2*n*(D.Sbox:ℝ)) := by
  have htri : ‖γ t‖≤‖γ t-y t‖+‖y t‖ := by
    calc ‖γ t‖ = ‖(γ t-y t)+y t‖ := by congr 1; abel
         _ ≤ ‖γ t-y t‖+‖y t‖ := norm_add_le _ _
  have he := flow_error_at hH D hγ hy h0 t ht
  rw [dist_eq_norm] at he
  exact htri.trans_lt (add_lt_add_of_lt_of_le he (source_norm_bound hH D hy t ht))

/-- Numerical margins in the compilation datum give a full unit of plateau clearance. -/
theorem compiled_plateau {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    {H : ℝ → E n → ℝ} (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2))
    (D : CompilationDatum n k C c s H) (hbR : D.bR<1)
    (hB : 2*((2*n+1:ℕ):ℝ)*(D.Sbox:ℝ)+4<D.B)
    {γ y : ℝ → E n} (hγ : IsIntegralCurveOn γ (Problem.hamVF D.Hfin) (Icc 0 1))
    (hy : IsIntegralCurveOn y (Problem.hamVF H) (Icc 0 1)) (h0 : γ 0=y 0)
    (hinit : ‖y 0‖+2<(D.B:ℝ)/2) (t : ℝ) (ht : t∈Icc 0 1) :
    ‖γ t‖+1<(D.B:ℝ)/2 := by
  have hS : (0:ℝ)<D.Sbox := by exact_mod_cast D.Sbox_pos
  have hsupp : 2*n*(D.Sbox:ℝ)+2<(D.B:ℝ)/2 := by
    push_cast at hB
    nlinarith
  have hmax : max ‖y 0‖ (2*n*(D.Sbox:ℝ))+2<(D.B:ℝ)/2 := by
    rcases le_total ‖y 0‖ (2*n*(D.Sbox:ℝ)) with h | h
    · rw [max_eq_right h]; exact hsupp
    · rw [max_eq_left h]; exact hinit
  have hb : (D.bR:ℝ)<1 := by exact_mod_cast hbR
  have hh := compiled_norm_lt hH D hγ hy h0 t ht
  linarith

/-- There are compilation data whose genuine cutoff-polynomial trajectories have a
uniform unit of clearance from the spatial plateau boundary, for every closed source ball.
No trajectory or tube property is an input hypothesis. -/
theorem exists_compilationDatum_plateau {n k : ℕ} {C₀ C : ℝ}
    {c : Fin k → ℝ} {s : Fin k → E n} {H : ℝ → E n → ℝ}
    (hpack : PackingSpec n k C₀ c s H) (hC₀ : 0<C₀) (hC : C₀<C) :
    ∃ D : CompilationDatum n k C c s H,
      PackingSpec n k C c s D.Hfin ∧
      ∀ i,∀ x∈capBall (s i) (c i),∀ γ : ℝ → E n,γ 0=x →
        IsIntegralCurveOn γ (Problem.hamVF D.Hfin) (Icc 0 1) →
        ∀ t∈Icc (0:ℝ) 1,‖γ t‖+1<(D.B:ℝ)/2 := by
  classical
  let R : ℝ := 1+∑ i, (‖s i‖+Real.sqrt (c i/Real.pi))
  have hsrc : ∀ i,∀ x∈capBall (s i) (c i),‖x‖≤R := by
    intro i x hx
    have hr : ‖x-s i‖≤Real.sqrt (c i/Real.pi) := by
      apply Real.le_sqrt_of_sq_le
      apply (le_div_iff₀ Real.pi_pos).mpr
      change Real.pi*‖x-s i‖^2≤c i at hx
      nlinarith
    have hsum := Finset.single_le_sum
      (f:=fun i => ‖s i‖+Real.sqrt (c i/Real.pi))
      (fun j _ => add_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) (Finset.mem_univ i)
    have htri : ‖x‖≤‖x-s i‖+‖s i‖ := by
      calc ‖x‖ = ‖(x-s i)+s i‖ := by congr 1; abel
           _ ≤ ‖x-s i‖+‖s i‖ := norm_add_le _ _
    change ‖x‖≤1+∑ j, (‖s j‖+Real.sqrt (c j/Real.pi))
    linarith
  obtain ⟨Bmin,hBmin⟩ := exists_nat_gt (2*(R+2))
  obtain ⟨D,hDB,hδ,hBl,hCeq,hbR⟩ :=
    exists_compilationDatum_with_margin hpack hC₀ hC Bmin 1 (by norm_num)
  refine ⟨D,finite_spec hpack.smooth D,?_⟩
  intro i x hx γ hγ0 hγ t ht
  obtain ⟨y,hy0,hy⟩ := hpack.exists_curve i x hx
  have hyOn := hy.isIntegralCurveOn (Icc (0:ℝ) 1)
  have hin : ‖y 0‖+2<(D.B:ℝ)/2 := by
    rw [hy0]
    have hh : (Bmin:ℝ)<D.B := by exact_mod_cast hDB
    linarith [hsrc i x hx]
  exact compiled_plateau hpack.smooth D hbR hBl hγ hyOn
    (hγ0.trans hy0.symm) hin t ht

end SymplecticPacking.General.Compile
