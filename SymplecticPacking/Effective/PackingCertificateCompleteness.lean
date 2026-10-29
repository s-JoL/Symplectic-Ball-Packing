import SymplecticPacking.Effective.PackingCertificateCompletenessCore
import SymplecticPacking.Effective.PackingCertificateSoundness

/-!
# Completeness of the finite certificate search

Nonemptiness of the finite packing certificate search.
-/

noncomputable section
namespace SymplecticPacking.Effective.PackingCertificate
open Set Metric Problem PackingPolynomial
open scoped Topology NNReal

/-- A smaller smooth packing yields a finite candidate whose rational
Euler tables pass every source-cell test. The names are the original centre
names and the radius programs derived from the original capacity names. -/
theorem exists_finite_checks {n k : ℕ} {C₀ Cmid C : ℝ}
    {c : Fin k → ℝ} {s : Fin k → E n} {H : ℝ → E n → ℝ}
    (hpack : PackingSpec n k C₀ c s H) (hC₀ : 0 < C₀)
    (hCmid : C₀ < Cmid) (hC : Cmid < C) (hc : ∀ i, 0 < c i)
    {source : Fin k → Fin (2*n) → ℕ → ℚ}
    (hs : ∀ i j, Names (source i j) (s i j))
    {rq : Fin k → ℕ → ℚ} (hr : ∀ i, Names (rq i) (Real.sqrt (c i/Real.pi)))
    {target : ℕ → ℚ} (htarget : Names target (Real.sqrt (C/Real.pi))) :
    ∃ p B Q m N : ℕ, ∃ program : List ℕ,
      1 ≤ B ∧ 0 < Q ∧ 0 < N ∧
      (∀ i j, |(source i j p:ℝ)|+(outerRadius (2*n) (rq i) p:ℝ) < (Q:ℝ)) ∧
      ∀ i g, g < FiniteGrid.count (2*n) m →
        cellCheck N (table n B N (boxNodeCode (2*n) Q m g) program)
          (fun j => source i j p) (boxRadius Q m) (outerRadius (2*n) (rq i) p)
          (error (budget B (programExpression program)) (budget B (programExpression program))
            (budget B (programExpression program)) N (boxRadius Q m) 0)
          ((B:ℚ)/2) (innerRadius target p) = true := by
  classical
  obtain ⟨B,e,hB,hfinite,ν,μ,hν,hμ,hnear⟩ :=
    exists_compiled_source_neighbourhood hpack hC₀ hCmid hC
  let program : List ℕ := expressionProgram e
  have hprog : programExpression program=e := programExpression_expressionProgram e
  obtain ⟨Q,hQ,hbox⟩ := exists_uniform_source_box hs hr (fun i => Real.sqrt_nonneg _)
  obtain ⟨p,m,N,hN,hδ,he,hde,hp⟩ :=
    exists_certificate_precisions (2*n) Q (budget B e) hν hμ
  refine ⟨p,B,Q,m,N,program,hB,hQ,hN,fun i j => hbox p i j,?_⟩
  intro i g hg
  rw [hprog]
  let a : Fin (2*n) → ℚ := boxNode (2*n) Q m g
  let x := table n B N (boxNodeCode (2*n) Q m g) program
  let v := velocity n B N (boxNodeCode (2*n) Q m g) program
  have hx0 : x 0=a := by
    change ODECode.rationalState (ODECode.decodeState (2*n)
      (boxNodeCode (2*n) Q m g))=boxNode (2*n) Q m g
    rw [boxNodeCode,ODECode.decodeState_encodeState,boxNodeState_value]
  by_cases hout : outsideCheck a (fun j => source i j p) (boxRadius Q m)
      (outerRadius (2*n) (rq i) p)=false
  · have hρ : (0:ℚ) ≤ boxRadius Q m :=
      mul_nonneg (by positivity : (0:ℚ) ≤ 2*(Q:ℚ)) (radius_pos m).le
    obtain ⟨y,hyball,hay⟩ := nonexcluded_near_source (hs i) (hr i)
      (Real.sqrt_pos.2 (div_pos (hc i) Real.pi_pos)) p a hρ hout
    have hycap : l2Vector y ∈ capBall (s i) (c i) := by
      rw [l2Vector_sub] at hyball
      have hyvec : l2Vector (fun j => s i j)=s i := rfl
      rw [hyvec] at hyball
      change Real.pi*‖l2Vector y-s i‖^2 ≤ c i
      have hh := pow_le_pow_left₀ (norm_nonneg _) hyball 2
      rw [Real.sq_sqrt (div_nonneg (hc i).le Real.pi_pos.le)] at hh
      nlinarith [(le_div_iff₀ Real.pi_pos).mp hh]
    obtain ⟨γ,hγ0,D⟩ := exists_curve_bounds n B e hB (ODE.castVector a)
    have hγ : IsIntegralCurveOn γ (field n B e) (Icc 0 1) :=
      fun t ht => (D.derivative t ht).hasDerivWithinAt
    have hsafety := hnear γ hγ ⟨y,⟨i,hycap⟩,by
      rw [hγ0,dist_eq_norm]
      exact hay.trans_lt hδ⟩
    have hstep : ∀ j < N, ODE.castVector (x (j+1))=ODE.castVector (x j)+
        (1/(N:ℝ)) • ODE.castVector (v j) := fun j _ =>
      table_step n B N (boxNodeCode (2*n) Q m g) program hN j
    have hvalue : ∀ j < N, ODE.castVector (v j)=
        field n B e (ODE.gridTime N j) (ODE.castVector (x j)) := by
      intro j hj
      simpa only [hprog] using velocity_exact n B N (boxNodeCode (2*n) Q m g) program hN j
    have hstart : ODE.castVector (x 0)=γ 0 := by rw [hx0,hγ0]
    have hplat : ∀ t ∈ Icc (0:ℝ) 1, ∀ j, |γ t j|+1/2 < (((B:ℚ)/2:ℚ):ℝ) := by
      simpa only [Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat] using hsafety.1
    have hchecks := table_checks_of_margins D hN x v hstep hvalue hstart hρ hμ
      hplat hsafety.2 htarget p he hde hp
    change cellCheck N x (fun j => source i j p) (boxRadius Q m)
      (outerRadius (2*n) (rq i) p) (error (budget B e) (budget B e) (budget B e) N (boxRadius Q m) 0)
      ((B:ℚ)/2) (innerRadius target p)=true
    simpa only [cellCheck,hx0,hout,Bool.false_or,Bool.and_eq_true] using hchecks
  · have hout' : outsideCheck a (fun j => source i j p) (boxRadius Q m)
        (outerRadius (2*n) (rq i) p)=true := by
      cases hh : outsideCheck a (fun j => source i j p) (boxRadius Q m)
        (outerRadius (2*n) (rq i) p) <;> simp_all
    change cellCheck N x (fun j => source i j p) (boxRadius Q m)
      (outerRadius (2*n) (rq i) p) (error (budget B e) (budget B e) (budget B e) N (boxRadius Q m) 0)
      ((B:ℚ)/2) (innerRadius target p)=true
    simp only [cellCheck,hx0,hout',Bool.true_or]

end SymplecticPacking.Effective.PackingCertificate
