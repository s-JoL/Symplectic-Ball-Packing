import SymplecticPacking.Effective.PackingCertificateFieldCode
import SymplecticPacking.Effective.PackingCertificateCode
import SymplecticPacking.Effective.PackingCertificateOutput

/-!
# Soundness of the finite Euler certificate

From the exact rational Euler table to containment of output flows.
-/

noncomputable section
namespace SymplecticPacking.Effective.PackingCertificate
open Set Metric Problem RationalCode PackingPolynomial PackingPolynomialCode
open scoped Topology NNReal ContDiff
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem table_cellCheck_sound {d A L M N : ℕ}
    {F : ℝ → (Fin d → ℝ) → (Fin d → ℝ)} {γ : ℝ → Fin d → ℝ}
    (D : ODE.Bounds F γ (A:ℝ) (L:ℝ) (M:ℝ)) (hN : 0<N)
    (x v : ℕ → Fin d → ℚ)
    (hstep : ∀ i<N, ODE.castVector (x (i+1))=ODE.castVector (x i)+
      (1/(N:ℝ)) • ODE.castVector (v i))
    (hvalue : ∀ i<N, ODE.castVector (v i)=F (ODE.gridTime N i) (ODE.castVector (x i)))
    (s : Fin d → ℚ) {ρ r plateau target : ℚ} (hρ : 0≤ρ) (hr : 0≤r)
    (hcover : ‖ODE.castVector (x 0)-γ 0‖≤(ρ:ℝ))
    (hball : ‖l2Vector (γ 0-ODE.castVector s)‖≤(r:ℝ))
    (hc : cellCheck N x s ρ r (error A L M N ρ 0) plateau target=true) :
    (∀ t∈Icc (0:ℝ) 1,∀ j,|γ t j|<(plateau:ℝ)) ∧ ‖l2Vector (γ 1)‖<(target:ℝ) := by
  have hc' := cellCheck_of_covered hρ hr hcover hball hc
  have hv : ∀ i<N, ‖ODE.castVector (v i)-F (ODE.gridTime N i) (ODE.castVector (x i))‖≤0 := by
    intro i hi
    rw [hvalue i hi, sub_self, norm_zero]
  constructor
  · intro t ht j
    exact plateauCheck_sound D hN x v hρ le_rfl hstep
      (by simpa only [Rat.cast_zero] using hv) hcover hc'.1 ht j
  · have he := grid_error D hN (fun i => ODE.castVector (x i))
      (fun i => ODE.castVector (v i)) le_rfl hstep hv (le_rfl : N≤N)
    have htN : ODE.gridTime N N=1 := by simp [ODE.gridTime,hN.ne']
    rw [htN,norm_sub_rev] at he
    have hb := error_bound (A:=A) (L:=L) (M:=M) (N:=N) hρ (le_rfl:(0:ℚ)≤0)
    have hm : (0:ℝ)≤(M:ℝ)/N := by positivity
    have hdist : ‖γ 1-ODE.castVector (x N)‖≤(error A L M N ρ 0:ℝ) := by
      simp only [Rat.cast_zero,add_zero] at he hb
      have hmul := mul_le_mul_of_nonneg_right
        (show ‖ODE.castVector (x 0)-γ 0‖+(A+L*M:ℝ)/N≤(ρ:ℝ)+(A+L*M:ℝ)/N by linarith)
        (Real.exp_nonneg (L:ℝ))
      exact he.trans (hmul.trans (by linarith))
    exact targetCheck_sound (error_nonneg A L M N hρ le_rfl) hdist hc'.2

def candidateCode (B : ℕ) (program : List ℕ) : ℕ := Nat.pair B (Encodable.encode program)

def tableCode (n B N initial : ℕ) (program : List ℕ) (i : ℕ) : ℕ :=
  ODECode.iterate (2*n) N (candidateCode B program) (universalField n) initial i

def table (n B N initial : ℕ) (program : List ℕ) (i : ℕ) : Fin (2*n) → ℚ :=
  ODECode.rationalState (ODECode.decodeState (2*n) (tableCode n B N initial program i))

def velocity (n B N initial : ℕ) (program : List ℕ) (i : ℕ) : Fin (2*n) → ℚ :=
  ODECode.rationalState (ODECode.decodeState (2*n) (universalField n
    (Nat.pair (ODECode.timeCode N i)
      (Nat.pair (tableCode n B N initial program i) (candidateCode B program)))))

theorem table_step (n B N initial : ℕ) (program : List ℕ) (hN : 0<N) (i : ℕ) :
    ODE.castVector (table n B N initial program (i+1))=
      ODE.castVector (table n B N initial program i)+
        (1/(N:ℝ)) • ODE.castVector (velocity n B N initial program i) := by
  change ODECode.realState (ODECode.decodeState (2*n)
    (ODECode.step (2*n) N (candidateCode B program) (universalField n) i
      (tableCode n B N initial program i))) = _
  rw [ODECode.step,ODECode.decodeState_encode]
  exact ODECode.update_real hN _ _

theorem velocity_exact (n B N initial : ℕ) (program : List ℕ) (hN : 0<N) (i : ℕ) :
    ODE.castVector (velocity n B N initial program i)=
      field n B (programExpression program) (ODE.gridTime N i)
        (ODE.castVector (table n B N initial program i)) := by
  have h := universalField_real n B (ODECode.timeCode N i)
    (tableCode n B N initial program i) program
  rw [ODECode.timeCode_value hN,Rat.cast_div,Rat.cast_natCast] at h
  exact h

theorem cellFailure_sound {n B N initial source ρ r e plateau target : ℕ}
    (program : List ℕ) {γ : ℝ → Fin (2*n) → ℝ}
    (D : ODE.Bounds (field n B (programExpression program)) γ
      (budget B (programExpression program):ℝ) (budget B (programExpression program):ℝ)
      (budget B (programExpression program):ℝ))
    (hN : 0<N) (hρ : 0≤value ρ) (hr : 0≤value r)
    (he : value e=error (budget B (programExpression program))
      (budget B (programExpression program)) (budget B (programExpression program)) N (value ρ) 0)
    (hcover : ‖ODECode.realState (ODECode.decodeState (2*n) initial)-γ 0‖≤(value ρ:ℝ))
    (hball : ‖l2Vector (γ 0-ODECode.realState (ODECode.decodeState (2*n) source))‖≤(value r:ℝ))
    (hc : PackingCertificateCode.cellFailure (2*n) (universalField n) N
      (candidateCode B program) initial source ρ r e plateau target=0) :
    (∀ t∈Icc (0:ℝ) 1,∀ j,|γ t j|<(value plateau:ℝ)) ∧
      ‖l2Vector (γ 1)‖<(value target:ℝ) := by
  have ht := (PackingCertificateCode.cellFailure_zero (2*n) (universalField n)
    N (candidateCode B program) initial source ρ r e plateau target).mp hc
  rw [he] at ht
  exact table_cellCheck_sound D hN (table n B N initial program)
    (velocity n B N initial program) (fun i _ => table_step n B N initial program hN i)
    (fun i _ => velocity_exact n B N initial program hN i)
    (ODECode.rationalState (ODECode.decodeState (2*n) source)) hρ hr hcover hball ht

theorem output_curve_unique (n B : ℕ) (program : List ℕ) (hB : 0<B)
    {γ y : ℝ → E n}
    (hγ : IsIntegralCurveOn γ (Problem.hamVF (output n B (programExpression program)).hamiltonian) (Icc 0 1))
    (hy : IsIntegralCurveOn y (Problem.hamVF (output n B (programExpression program)).hamiltonian) (Icc 0 1))
    (h0 : γ 0=y 0) : Set.EqOn γ y (Icc (0:ℝ) 1) := by
  obtain ⟨K,M,hK,_⟩ := General.Compile.window_bounds
    (output_smooth n B (programExpression program)) (output_support n B (programExpression program) hB) 0
  have hv : ∀ t∈Ico (0:ℝ) 1, LipschitzOnWith K
      (Problem.hamVF (output n B (programExpression program)).hamiltonian t) Set.univ := by
    intro t ht
    exact (hK t (by simp only [Nat.cast_zero,zero_add,abs_le]; constructor <;> linarith [ht.1,ht.2])).lipschitzOnWith
  have hIci : ∀ t∈Ico (0:ℝ) 1, Icc (0:ℝ) 1∈nhdsWithin t (Ici t) := fun t ht =>
    Filter.mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl)
  exact ODE_solution_unique_of_mem_Icc_right hv
    (fun t ht => (hγ t ht).continuousWithinAt)
    (fun t ht => (hγ t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hIci t ht))
    (fun _ _ => Set.mem_univ _)
    (fun t ht => (hy t ht).continuousWithinAt)
    (fun t ht => (hy t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (hIci t ht))
    (fun _ _ => Set.mem_univ _) h0

theorem clipped_to_output_curve (n B : ℕ) (program : List ℕ) (hB : 0<B)
    {γ : ℝ → Fin (2*n) → ℝ}
    (hγ : ∀ t∈Icc (0:ℝ) 1,HasDerivAt γ
      (field n B (programExpression program) t (γ t)) t)
    (hplateau : ∀ t∈Icc (0:ℝ) 1,∀ j,|γ t j|<(B:ℝ)/2) :
    IsIntegralCurveOn (fun t => (WithLp.toLp 2 (γ t) : E n))
      (Problem.hamVF (output n B (programExpression program)).hamiltonian) (Icc 0 1) := by
  letI : ContinuousSMul ℝ (E n) := IsBoundedSMul.continuousSMul
  intro t ht
  let L : (Fin (2*n) → ℝ) →L[ℝ] E n :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (2*n) => ℝ)).symm.toContinuousLinearMap
  have hd := L.hasFDerivAt.comp_hasDerivAt t (hγ t ht)
  have heq := field_eq_output_of_plateau n B (programExpression program) hB ht
    (z:=(WithLp.toLp 2 (γ t):E n)) (by simpa using hplateau t ht)
  change HasDerivWithinAt (fun t => (WithLp.toLp 2 (γ t):E n))
    (Problem.hamVF (output n B (programExpression program)).hamiltonian t
      (WithLp.toLp 2 (γ t))) (Icc 0 1) t
  have hd' : HasDerivAt (fun t => (WithLp.toLp 2 (γ t):E n))
      (WithLp.toLp 2 (field n B (programExpression program) t (γ t))) t := hd
  rw [heq] at hd'
  exact hd'.hasDerivWithinAt

/-- Soundness of the finite source-by-grid certificate for the delivered
Hamiltonian. The assumptions describe only certified input enclosures and an
finite covering; they contain no packing predicate or result oracle. -/
theorem finite_cover_sound {n k J B N ρ e plateau target : ℕ}
    {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    (program : List ℕ) (nodes : Fin J → ℕ) (sources radii : Fin k → ℕ)
    (hB : 1≤B) (hN : 0<N) (hC : 0<C)
    (hρ : 0≤value ρ) (hr : ∀ i,0≤value (radii i))
    (he : value e=error (budget B (programExpression program))
      (budget B (programExpression program)) (budget B (programExpression program)) N (value ρ) 0)
    (hplateau : value plateau=(B:ℚ)/2)
    (htarget : (value target:ℝ)≤Real.sqrt (C/Real.pi))
    (hcover : ∀ i,∀ x∈capBall (s i) (c i),∃ a : Fin J,
      ‖ODECode.realState (ODECode.decodeState (2*n) (nodes a))-(fun j => x j)‖≤(value ρ:ℝ))
    (hsource : ∀ i,∀ x∈capBall (s i) (c i),
      ‖l2Vector ((fun j => x j)-ODECode.realState (ODECode.decodeState (2*n) (sources i)))‖≤
        (value (radii i):ℝ))
    (hcheck : ∀ i a,PackingCertificateCode.cellFailure (2*n) (universalField n) N
      (candidateCode B program) (nodes a) (sources i) ρ (radii i) e plateau target=0) :
    PackingSpec n k C c s (output n B (programExpression program)).hamiltonian := by
  have hBpos : 0<B := by omega
  let R : ℝ := (2*n:ℝ)*(3*(B:ℝ)/4)
  have hR : ∀ t (z : E n),R<‖z‖ →
      (output n B (programExpression program)).hamiltonian t z=0 :=
    output_support n B (programExpression program) hBpos
  refine ⟨output_smooth n B (programExpression program),
    ⟨closedBall 0 R,isCompact_closedBall _ _,fun t z hz =>
      hR t z (by simpa only [mem_closedBall,dist_zero_right,not_le] using hz)⟩,
    fun i x _ => output_exists_global n B (programExpression program) hBpos x,?_⟩
  intro i x hx Γ hΓ0 hΓ
  obtain ⟨a,ha⟩ := hcover i x hx
  obtain ⟨y,hy0,Dy⟩ := exists_curve_bounds n B (programExpression program) hB (fun j => x j)
  have hc := cellFailure_sound program Dy hN hρ (hr i) he
    (by simpa only [hy0] using ha)
    (by simpa only [hy0] using hsource i x hx) (hcheck i a)
  have hplateau' : (value plateau:ℝ)=(B:ℝ)/2 := by
    have hh := congrArg (fun q : ℚ => (q:ℝ)) hplateau
    simpa only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] using hh
  have hy : IsIntegralCurveOn (fun t => (WithLp.toLp 2 (y t):E n))
      (Problem.hamVF (output n B (programExpression program)).hamiltonian) (Icc 0 1) :=
    clipped_to_output_curve n B program hBpos Dy.derivative
      (by simpa only [hplateau'] using hc.1)
  have hy0E : (WithLp.toLp 2 (y 0):E n)=x := by
    rw [hy0]
  have heq := output_curve_unique n B program hBpos hΓ hy (by rw [hΓ0,hy0E])
  have hnorm : ‖Γ 1‖<Real.sqrt (C/Real.pi) := by
    rw [heq ⟨zero_le_one,le_rfl⟩]
    exact hc.2.trans_le htarget
  have hsq : ‖Γ 1‖^2<(Real.sqrt (C/Real.pi))^2 :=
    pow_lt_pow_left₀ hnorm (norm_nonneg _) (by norm_num)
  rw [Real.sq_sqrt (div_nonneg hC.le Real.pi_pos.le),lt_div_iff₀ Real.pi_pos] at hsq
  show Real.pi*‖Γ 1-0‖^2<C
  rw [sub_zero]
  nlinarith

end SymplecticPacking.Effective.PackingCertificate
