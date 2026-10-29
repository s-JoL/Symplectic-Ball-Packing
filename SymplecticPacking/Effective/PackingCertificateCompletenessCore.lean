import SymplecticPacking.Effective.PackingCertificateNeighbourhood
import SymplecticPacking.Effective.PackingCertificateGrid

/-!
# Existence of strict finite Euler certificates

Strict finite Euler certificates exist for the polynomial candidates.
-/

noncomputable section
namespace SymplecticPacking.Effective.PackingCertificate
open Set Filter Metric
open scoped Topology NNReal

/-- Independent input, spatial-mesh and time-mesh precisions can pay all
strict margins at once. These choices occur solely in the termination proof. -/
theorem exists_certificate_precisions (d Q H : ℕ) {ν μ : ℝ}
    (hν : 0 < ν) (hμ : 0 < μ) :
    ∃ p m N : ℕ, 0 < N ∧
      (2*d+3:ℕ)*(radius p:ℝ)+(d:ℝ)*(boxRadius Q m:ℝ) < ν ∧
      (error H H H N (boxRadius Q m) 0:ℝ) < 1/8 ∧
      (d:ℝ)*(error H H H N (boxRadius Q m) 0:ℝ) < μ/8 ∧
      2*(radius p:ℝ) < μ/4 := by
  let ε : ℝ := min (1/8) (μ/(8*((d:ℝ)+1)))
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hμ (by positivity))
  have hp1 : ∀ᶠ p : ℕ in atTop, (2*d+3:ℕ)*(radius p:ℝ) < ν/2 := by
    have ht := radius_tendsto.const_mul ((2*d+3:ℕ):ℝ)
    simpa only [mul_zero] using (tendsto_order.mp ht).2 (ν/2) (by linarith)
  have hp2 : ∀ᶠ p : ℕ in atTop, 2*(radius p:ℝ) < μ/4 := by
    have ht := radius_tendsto.const_mul (2:ℝ)
    simpa only [mul_zero] using (tendsto_order.mp ht).2 (μ/4) (by linarith)
  obtain ⟨p,hp,hpμ⟩ := (hp1.and hp2).exists
  have hρt : Tendsto (fun m => (boxRadius Q m:ℝ)) atTop (𝓝 0) := by
    simpa only [boxRadius,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,mul_zero] using
      radius_tendsto.const_mul (2*(Q:ℝ))
  have hm1 : ∀ᶠ m : ℕ in atTop, (d:ℝ)*(boxRadius Q m:ℝ) < ν/2 := by
    have ht := hρt.const_mul (d:ℝ)
    simpa only [mul_zero] using (tendsto_order.mp ht).2 (ν/2) (by linarith)
  have hm2 : ∀ᶠ m : ℕ in atTop, (boxRadius Q m:ℝ)*(4:ℝ)^H < ε/2 := by
    have ht := hρt.mul_const ((4:ℝ)^H)
    simpa only [zero_mul] using (tendsto_order.mp ht).2 (ε/2) (by linarith)
  obtain ⟨m,hm,hmε⟩ := (hm1.and hm2).exists
  let K : ℝ := ((H:ℝ)+(H:ℝ)*(H:ℝ))*(4:ℝ)^H+(H:ℝ)
  have hNt : Tendsto (fun N : ℕ => K/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat K
  have hNs : ∀ᶠ N : ℕ in atTop, K/(N:ℝ) < ε/2 :=
    (tendsto_order.mp hNt).2 (ε/2) (by linarith)
  obtain ⟨N,hN,hNK⟩ := ((eventually_gt_atTop 0).and hNs).exists
  have heq : (error H H H N (boxRadius Q m) 0:ℝ) =
      (boxRadius Q m:ℝ)*(4:ℝ)^H+K/(N:ℝ) := by
    simp only [error,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,
      Rat.cast_pow,Rat.cast_zero,Rat.cast_ofNat,add_zero,K]
    ring
  have he : (error H H H N (boxRadius Q m) 0:ℝ) < ε := by rw [heq]; linarith
  have he0 : 0 ≤ (error H H H N (boxRadius Q m) 0:ℝ) := by
    exact_mod_cast error_nonneg H H H N
      (show (0:ℚ) ≤ boxRadius Q m from mul_nonneg (by positivity : (0:ℚ) ≤ 2*(Q:ℚ)) (radius_pos m).le) (le_rfl : (0:ℚ) ≤ 0)
  have hde : (d:ℝ)*(error H H H N (boxRadius Q m) 0:ℝ) < μ/8 := by
    have hh := lt_of_lt_of_le he (min_le_right (1/8:ℝ) (μ/(8*((d:ℝ)+1))))
    have hmul := (lt_div_iff₀ (by positivity : 0 < 8*((d:ℝ)+1))).mp hh
    nlinarith
  exact ⟨p,m,N,hN,by linarith,lt_of_lt_of_le he (min_le_left _ _),hde,hpμ⟩

/-- One integer box contains every outer source enclosure at every input
precision. It is only a completeness bound; the checker still verifies its
finite rational enclosure inequalities. -/
theorem exists_uniform_source_box {d k : ℕ}
    {q : Fin k → Fin d → ℕ → ℚ} {s : Fin k → Fin d → ℝ}
    {rq : Fin k → ℕ → ℚ} {r : Fin k → ℝ}
    (hq : ∀ i j, Names (q i j) (s i j))
    (hrq : ∀ i, Names (rq i) (r i)) (hr : ∀ i, 0 ≤ r i) :
    ∃ Q : ℕ, 0 < Q ∧ ∀ p i j,
      |(q i j p:ℝ)|+(outerRadius d (rq i) p:ℝ) < (Q:ℝ) := by
  classical
  let A : ℝ := 1+∑ i, (‖s i‖+r i+((d:ℝ)+5))
  have hsum0 : 0 ≤ ∑ i, (‖s i‖+r i+((d:ℝ)+5)) :=
    Finset.sum_nonneg (fun i _ => by have := hr i; positivity)
  obtain ⟨Q,hQ⟩ := exists_nat_gt A
  have hQpos : (0:ℝ) < Q := by dsimp [A] at hQ; linarith
  refine ⟨Q,by exact_mod_cast hQpos,?_⟩
  intro p i j
  have hp : (radius p:ℝ) ≤ 1 := by
    rw [radius_cast]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hname := hq i j p
  have htri := abs_add_le ((q i j p:ℝ)-s i j) (s i j)
  rw [sub_add_cancel] at htri
  have hcoord : |s i j| ≤ ‖s i‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (s i) j
  have houter := (outerRadius_bounds (hrq i) d p).2
  push_cast at houter
  have hsum := Finset.single_le_sum
    (f := fun i => ‖s i‖+r i+((d:ℝ)+5))
    (fun i _ => by have := hr i; positivity) (Finset.mem_univ i)
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg d
  dsimp [A] at hQ
  nlinarith

/-- Exact Euler rows inherit strict plateau and terminal tests from a
trajectory with the neighbourhood margins. The rational error includes its
source-cell radius, even though the reference trajectory starts at the node. -/
theorem table_checks_of_margins {d H N : ℕ}
    {F : ℝ → (Fin d → ℝ) → (Fin d → ℝ)} {γ : ℝ → Fin d → ℝ}
    (D : ODE.Bounds F γ (H:ℝ) (H:ℝ) (H:ℝ)) (hN : 0 < N)
    (x v : ℕ → Fin d → ℚ)
    (hstep : ∀ i < N, ODE.castVector (x (i+1))=ODE.castVector (x i)+
      (1/(N:ℝ)) • ODE.castVector (v i))
    (hvalue : ∀ i < N, ODE.castVector (v i)=F (ODE.gridTime N i) (ODE.castVector (x i)))
    (hstart : ODE.castVector (x 0)=γ 0)
    {ρ plateau : ℚ} (hρ : 0 ≤ ρ) {R μ : ℝ} (hμ : 0 < μ)
    (hplateau : ∀ t ∈ Icc (0:ℝ) 1, ∀ j, |γ t j|+1/2 < (plateau:ℝ))
    (htarget : ‖l2Vector (γ 1)‖+μ < R)
    {rq : ℕ → ℚ} (hrq : Names rq R) (p : ℕ)
    (he : (error H H H N ρ 0:ℝ) < 1/8)
    (hde : (d:ℝ)*(error H H H N ρ 0:ℝ) < μ/8)
    (hp : 2*(radius p:ℝ) < μ/4) :
    plateauCheck N x (error H H H N ρ 0) plateau = true ∧
      targetCheck (x N) (error H H H N ρ 0) (innerRadius rq p) = true := by
  let e : ℚ := error H H H N ρ 0
  have he0 : (0:ℝ) ≤ e := by exact_mod_cast error_nonneg H H H N hρ (le_rfl : (0:ℚ) ≤ 0)
  have hv : ∀ i < N, ‖ODE.castVector (v i)-F (ODE.gridTime N i) (ODE.castVector (x i))‖ ≤ 0 := by
    intro i hi
    rw [hvalue i hi,sub_self,norm_zero]
  have hdist : ∀ i ≤ N, ‖ODE.castVector (x i)-γ (ODE.gridTime N i)‖ ≤ (e:ℝ) := by
    intro i hi
    have hh := grid_error D hN (fun i => ODE.castVector (x i))
      (fun i => ODE.castVector (v i)) le_rfl hstep hv hi
    rw [hstart,sub_self,norm_zero] at hh
    have hb := error_bound (A:=H) (L:=H) (M:=H) (N:=N) hρ (le_rfl : (0:ℚ) ≤ 0)
    have hρ' : (0:ℝ) ≤ ρ := by exact_mod_cast hρ
    simp only [Rat.cast_zero,add_zero,zero_add] at hh hb
    have hm : (0:ℝ) ≤ (H:ℝ)/N := by positivity
    have hmul := mul_le_mul_of_nonneg_right hρ' (Real.exp_nonneg (H:ℝ))
    change _ ≤ (error H H H N ρ 0:ℝ)
    nlinarith
  constructor
  · change decide (∀ i : Fin (N+1), ∀ j, |x i j|+e < plateau) = true
    apply decide_eq_true
    intro i j
    have hi : (i:ℕ) ≤ N := by omega
    have hc := (norm_le_pi_norm (ODE.castVector (x i)-γ (ODE.gridTime N i)) j).trans (hdist i hi)
    have hs := hplateau (ODE.gridTime N i) (ODE.gridTime_mem hN hi) j
    have htri := abs_add_le ((x i j:ℝ)-γ (ODE.gridTime N i) j) (γ (ODE.gridTime N i) j)
    simp only [Pi.sub_apply,Real.norm_eq_abs,ODE.castVector] at hc
    rw [sub_add_cancel] at htri
    have hh : |(x i j:ℝ)|+(e:ℝ) < (plateau:ℝ) := by change (e:ℝ) < 1/8 at he; linarith
    exact_mod_cast hh
  · have htN : ODE.gridTime N N=1 := by simp [ODE.gridTime,hN.ne']
    have hdn := hdist N le_rfl
    rw [htN] at hdn
    have hl := l2_norm_le_dim_mul he0 hdn
    rw [l2Vector_sub] at hl
    have htri : ‖l2Vector (ODE.castVector (x N))‖ ≤
        ‖l2Vector (ODE.castVector (x N))-l2Vector (γ 1)‖+‖l2Vector (γ 1)‖ := by
      simpa only [add_comm] using norm_le_insert' (l2Vector (ODE.castVector (x N))) (l2Vector (γ 1))
    have hR : 0 ≤ R := by linarith [norm_nonneg (l2Vector (γ 1))]
    have hinner := (innerRadius_bounds hrq hR p).1
    have hnorm : ‖l2Vector (ODE.castVector (x N))‖ < (innerRadius rq p:ℝ)-(d:ℝ)*e := by
      change (d:ℝ)*(e:ℝ) < μ/8 at hde
      linarith
    have hpos : 0 < (innerRadius rq p:ℝ)-(d:ℝ)*e := (norm_nonneg _).trans_lt hnorm
    have hsq : (sqNorm (x N):ℝ) < ((innerRadius rq p:ℝ)-(d:ℝ)*e)^2 := by
      rw [sqNorm_cast]
      exact (sq_lt_sq₀ (norm_nonneg _) hpos.le).2 hnorm
    change decide (0 < innerRadius rq p-(d:ℚ)*e ∧
      sqNorm (x N) < (innerRadius rq p-(d:ℚ)*e)^2) = true
    apply decide_eq_true
    constructor
    · exact_mod_cast hpos
    · exact_mod_cast hsq

end SymplecticPacking.Effective.PackingCertificate
