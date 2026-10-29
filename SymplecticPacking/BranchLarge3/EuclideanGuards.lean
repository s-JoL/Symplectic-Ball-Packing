import SymplecticPacking.BranchLarge3.UniformMoser

/-!
# Polynomial guards for the Euclidean transfers

Native polynomial guards and fixed bases for the six-dimensional Euclidean transfers.
-/

noncomputable section
namespace SymplecticPacking.BranchLarge3
open OAI.PackingSufficiencySupport OAI.PackingSufficiencySupport.CubicModel
open Set
open scoped ContDiff

def cubicBasis : Module.Basis ((Fin 2 ⊕ Fin 2) ⊕ Fin 2) ℝ CubicAmbient :=
  (Complex.basisOneI.prod Complex.basisOneI).prod Complex.basisOneI

def ambientBasis : Module.Basis (Σ _ : Fin 3, Fin 2) ℝ (Fin 3 → ℂ) :=
  Pi.basis fun _ => Complex.basisOneI

theorem guard_normSq_smooth : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
  change ContDiff ℝ ∞ (fun z : ℂ => z.re*z.re+z.im*z.im)
  exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)

/-- Squared Euclidean norm, written without a nonsmooth maximum of coordinate norms. -/
def sepEnergy (x : Fin 3 → ℂ) : ℝ := ∑ i, Complex.normSq (x i)

lemma sepEnergy_nonneg (x : Fin 3 → ℂ) : 0 ≤ sepEnergy x :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (x i)

lemma norm_sq_le_sepEnergy (x : Fin 3 → ℂ) : ‖x‖^2 ≤ sepEnergy x := by
  have h : ‖x‖ ≤ Real.sqrt (sepEnergy x) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply Real.le_sqrt_of_sq_le
    rw [Complex.sq_norm]
    exact Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (x j)) (Finset.mem_univ i)
  nlinarith [Real.sq_sqrt (sepEnergy_nonneg x),norm_nonneg x, Real.sqrt_nonneg (sepEnergy x)]

theorem sepEnergy_smooth : ContDiff ℝ ∞ sepEnergy :=
  ContDiff.sum fun i _ => guard_normSq_smooth.comp (contDiff_apply ℝ ℂ i)

/-- Clearing the distinguished-chart denominator leaves a polynomial guard. -/
def outerSeparationGuard (ρ : ℝ) (z : CubicAmbient) : ℝ :=
  1+Complex.normSq z.1.1+Complex.normSq z.1.2-(ρ^2/4)*Complex.normSq z.2

lemma distinguished_energy (z : CubicAmbient) (hz : z.2 ≠ 0) :
    sepEnergy (firstToDistinguished z) =
      (1+Complex.normSq z.1.1+Complex.normSq z.1.2)/Complex.normSq z.2 := by
  simp [sepEnergy,firstToDistinguished,Fin.sum_univ_succ,Complex.normSq_div,
    Complex.normSq_inv]
  ring

theorem outerSeparationGuard_smooth (ρ : ℝ) : ContDiff ℝ ∞ (outerSeparationGuard ρ) :=
  ((contDiff_const.add (guard_normSq_smooth.comp contDiff_fst.fst)).add
    (guard_normSq_smooth.comp contDiff_fst.snd)).sub
    (contDiff_const.mul (guard_normSq_smooth.comp contDiff_snd))

lemma outerSeparationGuard_positive_iff (ρ : ℝ) (z : CubicAmbient) (hz : z.2 ≠ 0) :
    0 < outerSeparationGuard ρ z ↔ ρ^2/4 < sepEnergy (firstToDistinguished z) := by
  rw [distinguished_energy z hz,lt_div_iff₀ (Complex.normSq_pos.mpr hz)]
  unfold outerSeparationGuard
  constructor <;> intro h <;> linarith

/-- Two polynomial guards for the outer bubble target in the distinguished chart. -/
def outerBubbleGuards (ρ : ℝ) : Fin 2 → ℝ × CubicAmbient → ℝ :=
  ![fun p => Complex.normSq p.2.2,fun p => outerSeparationGuard ρ p.2]

theorem outerBubbleGuards_smooth (ρ : ℝ) :
    ∀ i,ContDiff ℝ ∞ (outerBubbleGuards ρ i) := by
  intro i
  fin_cases i
  · exact guard_normSq_smooth.comp contDiff_snd.snd
  · exact (outerSeparationGuard_smooth ρ).comp contDiff_snd

lemma outerBubbleGuards_positive_iff (ρ : ℝ) (p : ℝ × CubicAmbient) :
    (∀ i,0<outerBubbleGuards ρ i p) ↔
      p.2.2≠0 ∧ ρ^2/4<sepEnergy (firstToDistinguished p.2) := by
  simp only [Fin.forall_fin_succ,outerBubbleGuards,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.cons_val_fin_one,Fin.forall_fin_zero,and_true]
  constructor
  · intro h
    have hz := Complex.normSq_pos.mp h.1
    exact ⟨hz,(outerSeparationGuard_positive_iff ρ p.2 hz).mp h.2⟩
  · intro h
    exact ⟨Complex.normSq_pos.mpr h.1,(outerSeparationGuard_positive_iff ρ p.2 h.1).mpr h.2⟩

/-- A single polynomial guard for the scaled bubble ball. -/
def innerBubbleGuards (ρ : ℝ) : Fin 1 → ℝ × (Fin 3 → ℂ) → ℝ :=
  fun _ p => ρ^2/4-sepEnergy ((p.1:ℂ) • p.2)

theorem innerBubbleGuards_smooth (ρ : ℝ) :
    ∀ i,ContDiff ℝ ∞ (innerBubbleGuards ρ i) := fun _ =>
  contDiff_const.sub (sepEnergy_smooth.comp
    ((Complex.ofRealCLM.contDiff.comp contDiff_fst).smul contDiff_snd))

lemma innerBubbleGuards_positive_iff (ρ : ℝ) (p : ℝ × (Fin 3 → ℂ)) :
    (∀ i,0 < innerBubbleGuards ρ i p) ↔ sepEnergy ((p.1:ℂ) • p.2)<ρ^2/4 := by
  simp [innerBubbleGuards,Fin.forall_fin_succ,sub_pos]

end SymplecticPacking.BranchLarge3
