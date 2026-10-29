import SymplecticPacking.Effective.PackingCertificateAlgorithm
import SymplecticPacking.Effective.PackingCertificateEpochInput
import SymplecticPacking.Effective.PackingCertificateEpochRecursive

/-!
# The Epoch machine

One machine reads only k and the original epsilon name and returns a finite
rational Hamiltonian satisfying the original Epoch packing condition.
-/

noncomputable section
namespace SymplecticPacking.Effective.PackingEpoch
open Set Metric Problem PackingSearch PackingCertificate

 theorem radius_eq_epoch (k : ℕ) {ε : ℝ} (hε : ε<1) :
    radius k ε=General.epochRadius k ε := by
  have hnonneg : 0≤(k:ℝ)/(1-ε/2) := div_nonneg (Nat.cast_nonneg k) (by linarith)
  unfold radius General.epochRadius General.epochR4
  rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,←Real.rpow_mul hnonneg]
  norm_num

 theorem target_names {ε : ℝ} (epsilon : ℕ → ℕ) (he : CodeName.Names epsilon ε)
    (h0 : 0<ε) (h1 : ε<1) {k : ℕ} (hk : 9≤k) :
    CodeName.Names (Family.slice (radiusCode epsilon (validEpsilon_of_names epsilon he h1)) k)
      (Real.sqrt ((Real.pi*General.epochRadius k ε^2)/Real.pi)) := by
  have hdiv : (Real.pi*General.epochRadius k ε^2)/Real.pi=General.epochRadius k ε^2 := by
    field_simp [Real.pi_ne_zero]
  rw [hdiv,Real.sqrt_sq_eq_abs,abs_of_pos (General.epochRadius_pos hk h0 h1)]
  simpa only [radius_eq_epoch k h1] using radiusCode_names epsilon (validEpsilon_of_names epsilon he h1) he h1 k

 theorem source_names (i : ℕ) : CodeName.Names
    (fun p=>sourceRadii (Nat.pair i p)) (Real.sqrt (Real.pi/Real.pi)) := by
  simpa only [div_self Real.pi_ne_zero,Real.sqrt_one] using sourceRadii_names i

/-- Geometry enters only this termination proof. The checker reads the native
radius family and rational integer source data. -/
 theorem exists_epoch_stage {ε : ℝ} (epsilon : ℕ → ℕ) (he : CodeName.Names epsilon ε)
    {k : ℕ} (hk : 9≤k) (h0 : 0<ε) (h1 : ε<1) :
    ∃ st,familyStageFailure centres sourceRadii (radiusCode epsilon (validEpsilon_of_names epsilon he h1)) k st=0 := by
  have hA:=General.epoch_admissible hk h0 h1
  obtain ⟨C₀,hC₀,hC₀C,hpack⟩ :=
    (General.packing_main hA (General.epoch_disjoint k)).exists_smaller_target hA.C_pos
  exact PackingSearch.exists_stage centres sourceRadii (Family.slice (radiusCode epsilon (validEpsilon_of_names epsilon he h1)) k)
    hpack hC₀ (show C₀<(C₀+(Real.pi*General.epochRadius k ε^2))/2 by linarith)
    (show (C₀+(Real.pi*General.epochRadius k ε^2))/2<Real.pi*General.epochRadius k ε^2 by linarith)
    hA.c_pos (fun i j=>centres_names i.val j) (fun i=>source_names i.val)
    (target_names epsilon he h0 h1 hk)

def selectedStage {ε : ℝ} (epsilon : ℕ → ℕ) (he : CodeName.Names epsilon ε)
    {k : ℕ} (hk : 9≤k) (h0 : 0<ε) (h1 : ε<1) : ℕ :=
  Nat.find (exists_epoch_stage epsilon he hk h0 h1)

def compiledCode {ε : ℝ} (epsilon : ℕ → ℕ) (he : CodeName.Names epsilon ε)
    {k : ℕ} (hk : 9≤k) (h0 : 0<ε) (h1 : ε<1) : ℕ :=
  programCode (selectedStage epsilon he hk h0 h1)

/-- k is the input of this one machine, not a frozen external parameter. -/
def machine (epsilon : ℕ → ℕ) (hv : ValidEpsilon epsilon) : ℕ →. ℕ :=
  familyProgramSearch centres sourceRadii (radiusCode epsilon hv)

 theorem machine_recursive (epsilon : ℕ → ℕ) (hv : ValidEpsilon epsilon) :
    Nat.RecursiveIn (originalOracles epsilon) (machine epsilon hv) :=
  familyProgramSearch_recursive (Oracle.of_computable primitive_centres.to_comp)
    (Oracle.of_computable (Computable.const _)) (radiusCode_recursive epsilon hv)

 theorem machine_halts {ε : ℝ} (epsilon : ℕ → ℕ) (he : CodeName.Names epsilon ε)
    {k : ℕ} (hk : 9≤k) (h0 : 0<ε) (h1 : ε<1) :
    compiledCode epsilon he hk h0 h1∈machine epsilon (validEpsilon_of_names epsilon he h1) k :=
  familyProgramSearch_halts (exists_epoch_stage epsilon he hk h0 h1)

 private theorem stage_hamiltonian_eq_code (st : ℕ) :
    (stageOutput 2 st).hamiltonian=codeHamiltonian 2 (programCode st) := by
  simp only [stageOutput,codeHamiltonian,programCode,PackingCertificate.candidateCode,
    Nat.unpair_pair,PackingStateList.decodeList,Encodable.encodek,Option.getD_some]

 theorem compiled_packing_spec {ε : ℝ} (epsilon : ℕ → ℕ) (he : CodeName.Names epsilon ε)
    {k : ℕ} (hk : 9≤k) (h0 : 0<ε) (h1 : ε<1) :
    PackingSpec 2 k (Real.pi*General.epochRadius k ε^2) (fun _=>Real.pi)
      (fun i=>epochCenter i) (codeHamiltonian 2 (compiledCode epsilon he hk h0 h1)) := by
  have hA:=General.epoch_admissible hk h0 h1
  have hpass:=Nat.find_spec (exists_epoch_stage epsilon he hk h0 h1)
  have hh:=stage_sound centres sourceRadii (Family.slice (radiusCode epsilon (validEpsilon_of_names epsilon he h1)) k)
    hpass hA.C_pos hA.c_pos (fun i j=>centres_names i.val j)
    (fun i=>source_names i.val) (target_names epsilon he h0 h1 hk)
  simpa only [stage_hamiltonian_eq_code,compiledCode,selectedStage] using hh

/-- The returned code satisfies the original closed-unit-ball and density
condition, with no supplied target-radius or capacity-name oracle. -/
 theorem compiled_epoch_spec {ε : ℝ} (epsilon : ℕ → ℕ) (he : CodeName.Names epsilon ε)
    {k : ℕ} (hk : 9≤k) (h0 : 0<ε) (h1 : ε<1) :
    Problem.EpochSpecR k ε (General.epochRadius k ε)
      (codeHamiltonian 2 (compiledCode epsilon he hk h0 h1)) := by
  have hP:=compiled_packing_spec epsilon he hk h0 h1
  have hR:=General.epochRadius_pos hk h0 h1
  have hb:=General.epochR4_bounds hk h0 h1
  refine ⟨hP.smooth,hP.compactSupport,hR,?_,?_,?_⟩
  · rw [General.epochRadius_pow_four hk h0 h1,hb.2]
    linarith
  · intro i hi x hx
    exact hP.exists_curve ⟨i,hi⟩ x (General.mem_capBall_pi_iff.2 hx)
  · intro i hi x hx γ hγ₀ hγ
    have h:=hP.maps_into ⟨i,hi⟩ x (General.mem_capBall_pi_iff.2 hx) γ hγ₀ hγ
    simp only [capBallOpen,mem_setOf_eq,sub_zero] at h
    rw [mem_closedBall_zero_iff]
    have hh : ‖γ 1‖^2<General.epochRadius k ε^2 :=
      lt_of_mul_lt_mul_left h Real.pi_pos.le
    exact ((pow_lt_pow_iff_left₀ (norm_nonneg _) hR.le (by norm_num)).1 hh).le

#check_explicit machine
#check_explicit compiledCode
end SymplecticPacking.Effective.PackingEpoch
