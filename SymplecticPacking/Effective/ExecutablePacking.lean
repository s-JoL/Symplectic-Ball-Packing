import SymplecticPacking.Effective.PackingCertificateEpochAlgorithm

/-!
Native finite-certificate search. The executable arithmetic is the existing
verified checker, with computable exact input names and rational output radius.
The search is a computable total definition; geometric existence is used only
in erased proofs of termination and of the returned full packing certificate.
-/

namespace NativePacking
open SymplecticPacking SymplecticPacking.Effective
open RationalCode PackingSearch PackingCertificateCode

def centres (x : ℕ) : ℕ :=
  if (Nat.unpair x).2 = 0 then dimCode (3 * (Nat.unpair (Nat.unpair x).1).1)
  else dimCode 0

def units (_ : ℕ) : ℕ := dimCode 1

def RadiusOK (k : ℕ) (epsilon : ℚ) (code : ℕ) : Prop :=
  0 < value code ∧ (k : ℚ) / (1-epsilon/2) < (value code)^4 ∧
    (value code)^4 < (k : ℚ) / (1-epsilon)

instance (k : ℕ) (epsilon : ℚ) (code : ℕ) : Decidable (RadiusOK k epsilon code) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem exists_radius {k : ℕ} (hk : 9 ≤ k) {q : ℚ} (h0 : 0 < q) (h1 : q < 1) :
    ∃ code, RadiusOK k q code := by
  have hkq : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  let L : ℚ := k / (1-q/2)
  let U : ℚ := k / (1-q)
  have hL : 0 < L := div_pos hkq (by linarith)
  have hU : 0 < U := div_pos hkq (by linarith)
  have hLU : L < U := div_lt_div_of_pos_left hkq (by linarith) (by linarith)
  let a : ℝ := Real.sqrt (Real.sqrt (L : ℝ))
  let b : ℝ := Real.sqrt (Real.sqrt (U : ℝ))
  have ha : 0 < a := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hL))
  have hb : 0 < b := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hU))
  have ha4 : a^4 = (L : ℝ) := by
    have h := Real.sq_sqrt (Real.sqrt_nonneg (L : ℝ))
    have h' := Real.sq_sqrt (show (0 : ℝ) ≤ L by exact_mod_cast hL.le)
    change (Real.sqrt (Real.sqrt (L : ℝ)))^4 = _
    nlinarith [sq_nonneg (Real.sqrt (Real.sqrt (L : ℝ)))]
  have hb4 : b^4 = (U : ℝ) := by
    have h := Real.sq_sqrt (Real.sqrt_nonneg (U : ℝ))
    have h' := Real.sq_sqrt (show (0 : ℝ) ≤ U by exact_mod_cast hU.le)
    change (Real.sqrt (Real.sqrt (U : ℝ)))^4 = _
    nlinarith [sq_nonneg (Real.sqrt (Real.sqrt (U : ℝ)))]
  have hab : a < b := by
    by_contra hn
    have hh := pow_le_pow_left₀ hb.le (le_of_not_gt hn) 4
    rw [ha4, hb4] at hh
    exact (not_le_of_gt (show (L : ℝ) < U by exact_mod_cast hLU)) hh
  obtain ⟨r, har, hrb⟩ := exists_rat_btwn hab
  have hr : (0 : ℝ) < r := ha.trans har
  have hlr := (pow_lt_pow_iff_left₀ ha.le hr.le (by norm_num : 4 ≠ 0)).2 har
  have hru := (pow_lt_pow_iff_left₀ hr.le hb.le (by norm_num : 4 ≠ 0)).2 hrb
  refine ⟨ofRat r, ?_⟩
  simp only [RadiusOK, value_ofRat]
  rw [ha4] at hlr
  rw [hb4] at hru
  exact ⟨by exact_mod_cast hr, by exact_mod_cast hlr, by exact_mod_cast hru⟩

def radiusTrial (k : ℕ) (q : ℚ) (bits : ℕ) : ℕ :=
  let U : ℚ := k / (1-q)
  let scale := 2^bits
  let numerator := U.num.toNat * scale^4
  let m := Nat.sqrt (Nat.sqrt (numerator / U.den))
  let r : ℚ := (m : ℚ) / scale
  ofRat (if r^4 < U then r else (m-1 : ℕ) / (scale : ℚ))

def radiusTrials (k : ℕ) (q : ℚ) : ℕ → ℕ → Option {code // RadiusOK k q code}
  | _, 0 => none
  | bits, fuel+1 =>
    let code := radiusTrial k q bits
    if h : RadiusOK k q code then some ⟨code, h⟩
    else radiusTrials k q (max 1 (2*bits)) fuel

def chooseRadius {k : ℕ} (hk : 9 ≤ k) {q : ℚ} (h0 : 0 < q) (h1 : q < 1) :
    {code // RadiusOK k q code} :=
  match radiusTrials k q 0 (8*(k.log2+q.den.log2+q.num.natAbs.log2+1)) with
  | some code => code
  | none => ⟨Nat.find (exists_radius hk h0 h1), Nat.find_spec (exists_radius hk h0 h1)⟩

theorem centres_names (i : ℕ) (j : Fin 4) : CodeName.Names
    (fun p => centres (Nat.pair (Nat.pair i p) j.val)) (Problem.epochCenter i j) := by
  simpa only [centres, PackingEpoch.centres] using PackingEpoch.centres_names i j

theorem units_names (i : ℕ) : CodeName.Names (fun p => units (Nat.pair i p)) 1 := by
  simpa only [units, PackingEpoch.sourceRadii] using PackingEpoch.sourceRadii_names i

theorem target_names (R : ℚ) (hR : 0 < R) :
    Names (fun _ => value (ofRat R)) (Real.sqrt ((Real.pi*(R:ℝ)^2)/Real.pi)) := by
  have hh : (Real.pi*(R:ℝ)^2)/Real.pi = (R:ℝ)^2 := by field_simp
  rw [hh, Real.sqrt_sq_eq_abs, abs_of_pos (show (0:ℝ)<R by exact_mod_cast hR)]
  simpa only [value_ofRat] using names_rational R

theorem exists_stage {k : ℕ} (hk : 9 ≤ k) {q : ℚ} (h0 : 0 < q) (h1 : q < 1)
    {code : ℕ} (hcode : RadiusOK k q code) :
    ∃ st, stageFailure centres units (fun _ => code) 2 k st = 0 := by
  let R := value code
  have hq0 : (0:ℝ) < q := by exact_mod_cast h0
  have hq1 : (q:ℝ) < 1 := by exact_mod_cast h1
  have hR : (0:ℝ) < R := by exact_mod_cast hcode.1
  have hr := General.epochRadius_pos hk hq0 hq1
  have hr4 := General.epochRadius_pow_four hk hq0 hq1
  have hlow : General.epochRadius k (q:ℝ)^4 < (R:ℝ)^4 := by
    rw [hr4, General.epochR4]
    exact_mod_cast hcode.2.1
  have hlt : General.epochRadius k (q:ℝ) < (R:ℝ) :=
    (pow_lt_pow_iff_left₀ hr.le hR.le (by norm_num : 4 ≠ 0)).1 hlow
  let C₀ := Real.pi*General.epochRadius k (q:ℝ)^2
  let C := Real.pi*(R:ℝ)^2
  have hC : C₀ < C := by
    apply mul_lt_mul_of_pos_left _ Real.pi_pos
    exact (pow_lt_pow_iff_left₀ hr.le hR.le (by norm_num : 2 ≠ 0)).2 hlt
  have hA := General.epoch_admissible hk hq0 hq1
  have ht : Names (fun _ => value code) (Real.sqrt (C/Real.pi)) := by
    simpa only [R, value_ofRat] using target_names R hcode.1
  exact PackingSearch.exists_stage centres units (fun _ => code)
    (General.packing_main hA (General.epoch_disjoint k)) hA.C_pos
    (show C₀ < (C₀+C)/2 by linarith) (show (C₀+C)/2 < C by linarith)
    hA.c_pos (fun i j => centres_names i.val j)
    (fun i => by simpa only [CodeName.Names, div_self Real.pi_ne_zero, Real.sqrt_one] using units_names i.val) ht

/-- Stop at the first failed finite check; do not construct the full sum. -/
def allBelow (test : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n+1 => if test n then allBelow test n else false

theorem allBelow_iff (test : ℕ → Bool) (n : ℕ) :
    allBelow test n = true ↔ ∀ i < n, test i = true := by
  induction n with
  | zero => simp [allBelow]
  | succ n ih =>
      simp only [allBelow, Bool.ite_false_right, Bool.and_eq_true, decide_eq_true_eq,
        ih, Nat.forall_lt_succ_right]
      exact and_comm

/-- Equivalent to the original sum-of-failures checker, with early rejection. -/
def checkStage (k code st : ℕ) : Bool :=
  let a := decodeCandidate st
  if 0 < a.2.1 ∧ 0 < a.2.2.1 ∧ 0 < a.2.2.2.2.1 then
    if allBelow (fun i => decide
        (enclosureTerm centres units (Nat.pair (Nat.pair 2 st) i) = 0)) k then
      allBelow (fun i => allBelow (fun g => decide
        (cellTerm centres units (fun _ => code)
          (Nat.pair (Nat.pair (Nat.pair 2 st) i) g) = 0))
        (FiniteGrid.count 4 a.2.2.2.1)) k
    else false
  else false

theorem checkStage_iff (k code st : ℕ) :
    checkStage k code st = true ↔ stageFailure centres units (fun _ => code) 2 k st = 0 := by
  rw [stageFailure_zero]
  unfold checkStage
  dsimp only
  by_cases h : 0 < (decodeCandidate st).2.1 ∧ 0 < (decodeCandidate st).2.2.1 ∧
      0 < (decodeCandidate st).2.2.2.2.1
  · simp only [if_pos h, Bool.ite_false_right, Bool.and_eq_true, decide_eq_true_eq, allBelow_iff]
    constructor
    · rintro ⟨he,hc⟩
      exact ⟨by omega,h.2.1,h.2.2,he,hc⟩
    · rintro ⟨_,_,_,he,hc⟩
      exact ⟨he,hc⟩
  · simp only [if_neg h, Bool.false_eq_true, false_iff]
    rintro ⟨hB,hQ,hN,_,_⟩
    exact h ⟨by omega,hQ,hN⟩

def identitySeed (k : ℕ) : ℕ :=
  let Q := 3*k+8
  encodeCandidate (0, (64*Q, (Q, (2, (1, [])))))

def chooseStage {k : ℕ} (hk : 9 ≤ k) {q : ℚ} (h0 : 0 < q) (h1 : q < 1)
    {code : ℕ} (hcode : RadiusOK k q code) :
    {st // stageFailure centres units (fun _ => code) 2 k st = 0} :=
  let seed := identitySeed k
  if h : checkStage k code seed = true then ⟨seed, (checkStage_iff k code seed).mp h⟩
  else
    let hex : ∃ st, checkStage k code st = true := by
      obtain ⟨st, hst⟩ := exists_stage hk h0 h1 hcode
      exact ⟨st, (checkStage_iff k code st).mpr hst⟩
    ⟨Nat.find hex, (checkStage_iff k code (Nat.find hex)).mp (Nat.find_spec hex)⟩

private theorem stage_hamiltonian_eq_code (st : ℕ) :
    (stageOutput 2 st).hamiltonian = codeHamiltonian 2 (programCode st) := by
  simp only [stageOutput, codeHamiltonian, programCode, PackingCertificate.candidateCode,
    Nat.unpair_pair, PackingStateList.decodeList, Encodable.encodek, Option.getD_some]

theorem stage_epoch_spec {k : ℕ} (_hk : 9 ≤ k) {q : ℚ} (_h0 : 0 < q) (h1 : q < 1)
    {code st : ℕ} (hcode : RadiusOK k q code)
    (hpass : stageFailure centres units (fun _ => code) 2 k st = 0) :
    Problem.EpochSpecR k (q:ℝ) (value code:ℝ) (codeHamiltonian 2 (programCode st)) := by
  let R := value code
  have hR : (0:ℝ) < R := by exact_mod_cast hcode.1
  have ht : Names (fun _ => value code) (Real.sqrt ((Real.pi*(R:ℝ)^2)/Real.pi)) := by
    simpa only [R, value_ofRat] using target_names R hcode.1
  have hP := stage_sound centres units (fun _ => code) hpass
    (show (0:ℝ) < Real.pi*(R:ℝ)^2 by positivity) (fun _ => Real.pi_pos)
    (fun i j => centres_names i.val j)
    (fun i => by simpa only [CodeName.Names, div_self Real.pi_ne_zero, Real.sqrt_one] using units_names i.val) ht
  rw [stage_hamiltonian_eq_code] at hP
  have hdensity : 1-(q:ℝ) < (k:ℝ)/(R:ℝ)^4 := by
    have hd : (0:ℝ) < 1-(q:ℝ) := by exact_mod_cast (sub_pos.mpr h1)
    have hu : (R:ℝ)^4 < (k:ℝ)/(1-(q:ℝ)) := by exact_mod_cast hcode.2.2
    have hm := (lt_div_iff₀ hd).mp hu
    exact (lt_div_iff₀ (pow_pos hR 4)).mpr (by nlinarith)
  refine ⟨hP.smooth, hP.compactSupport, hR, hdensity, ?_, ?_⟩
  · intro i hi x hx
    exact hP.exists_curve ⟨i,hi⟩ x (General.mem_capBall_pi_iff.mpr hx)
  · intro i hi x hx γ hγ0 hγ
    have hh := hP.maps_into ⟨i,hi⟩ x (General.mem_capBall_pi_iff.mpr hx) γ hγ0 hγ
    simp only [Problem.capBallOpen, Set.mem_ofPred_eq, sub_zero] at hh
    rw [Metric.mem_closedBall, dist_zero_right]
    have hs : ‖γ 1‖^2 < (R:ℝ)^2 := lt_of_mul_lt_mul_left hh Real.pi_pos.le
    exact ((pow_lt_pow_iff_left₀ (norm_nonneg _) hR.le (by norm_num : 2 ≠ 0)).mp hs).le

structure Output (k : ℕ) (epsilon : ℝ) where
  radius : ℚ
  stage : ℕ
  certificate : Problem.EpochSpecR k epsilon (radius:ℝ)
    (codeHamiltonian 2 (programCode stage))

/-- Total native extraction: all geometry occurs in erased termination proofs. -/
def solveRational {k : ℕ} (hk : 9 ≤ k) {q : ℚ} (h0 : 0 < q) (h1 : q < 1) :
    Output k (q:ℝ) :=
  let R := chooseRadius hk h0 h1
  let st := chooseStage hk h0 h1 R.property
  ⟨value R.val, st.val, stage_epoch_spec hk h0 h1 R.property st.property⟩

def lowerEpsilon {epsilon : ℝ} (name : ℕ → ℕ) (he : CodeName.Names name epsilon)
    (h0 : 0 < epsilon) (h1 : epsilon < 1) :
    {q : ℚ // 0 < q ∧ q < 1 ∧ (q:ℝ) ≤ epsilon} := by
  have hex : ∃ p, radius (p+128) < value (name (p+128)) := by
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (eventually_positive_certificate he h0)
    exact ⟨N,hN (N+128) (by omega)⟩
  let p := Nat.find hex
  let q := value (name (p+128))-radius (p+128)
  have hq : 0 < q := sub_pos.mpr (Nat.find_spec hex)
  have hle : (q:ℝ) ≤ epsilon := by
    have hh := (abs_le.mp (he (p+128))).2
    dsimp only [q]
    push_cast
    linarith
  exact ⟨q, hq, by exact_mod_cast (hle.trans_lt h1), hle⟩

theorem epoch_mono {k : ℕ} {q epsilon R : ℝ} {H : ℝ → Problem.E 2 → ℝ}
    (hle : q ≤ epsilon) (h : Problem.EpochSpecR k q R H) : Problem.EpochSpecR k epsilon R H := by
  exact ⟨h.smooth, h.compactSupport, h.radius_pos, by linarith [h.density], h.exists_curve, h.maps_into⟩

/-- The general epsilon input is a real name, not a restricted rational sample. -/
def solveName {k : ℕ} (hk : 9 ≤ k) {epsilon : ℝ} (name : ℕ → ℕ)
    (he : CodeName.Names name epsilon) (h0 : 0 < epsilon) (h1 : epsilon < 1) : Output k epsilon :=
  let q := lowerEpsilon name he h0 h1
  let out := solveRational hk q.property.1 q.property.2.1
  ⟨out.radius, out.stage, epoch_mono q.property.2.2 out.certificate⟩

end NativePacking
