import SymplecticPacking.HighDim.Comparator.FixedPoint
import SymplecticPacking.HighDim.Comparator.Smoothing
import SymplecticPacking.HighDim.Comparator.Realisation

/-!
# The comparison datum (paper def:mech-datum, thm:cmp-main)

A comparison datum for `(Δ, P)` with gap `γ > 0` is a smooth toric function `K` and a fibre
generator `Q` whose time-one map `q` preserves `V_Δ`, has outer-face collars, and satisfies
`(K − P)(p(q(w))) ≤ K(p(w)) − γ` on `V_Δ`.

`comparatorDatum` is the explicit datum of thm:cmp-main: `K_N` from the finite comparator
(as data, `KData`), `F_0 = K_N − P`, `F_j = R_j F_{j−1}`, generators `Q^{(j)}` realising
`R_j` on `F_{j−1}` up to `e = d/(8(m+1))`, concatenated so that `q = q^{(1)} ∘ ⋯ ∘ q^{(m)}`
(stage `m` first), and `K` the log-sum-exp smoothing of `K_N` within `d/32`.
Gap: `7d/8 − m e − 2·d/32 ≥ 11d/16`.
-/

noncomputable section

namespace SymplecticPacking.HighDim

open Set
open OAI.PackingSufficiencySupport.Hamiltonian (planeMoments)
open OAI.PackingSufficiencySupport.MomentPolytope (Moments region planeRegion)
open scoped ContDiff

variable {m q : ℕ}

/-- A comparison datum: toric function `K` and fibre generator `Q`. -/
structure ComparisonDatum (m : ℕ) where
  K : Moments m → ℝ
  Q : ℝ → Fibre m → ℝ
  /-- A numerical budget retained by the later handle construction. -/
  reserve : ℝ

namespace ComparisonDatum

/-- The time-one map `q`. -/
def qMap (D : ComparisonDatum m) : Fibre m → Fibre m := isoOf D.Q 1

/-- def:mech-datum. -/
structure Spec (D : ComparisonDatum m) (Δ : Polytope m q) (P : Moments m → ℝ) (γ : ℝ) :
    Prop where
  K_smooth : ContDiff ℝ ∞ D.K
  gen : GenSpec D.Q
  preserves : PreservesRegion Δ D.Q
  collar : FaceCollar Δ D.Q
  gap_pos : 0 < γ
  gap : ∀ w ∈ planeRegion Δ.b Δ.ℓ,
    D.K (planeMoments (D.qMap w)) - P (planeMoments (D.qMap w)) ≤ D.K (planeMoments w) - γ
  reserve_pos : 0 < D.reserve
  reserve_le_gap : D.reserve ≤ γ

end ComparisonDatum

namespace CmpInput

variable (I : CmpInput m q) (negP : PolyFn m)

/-- `K_r` as data: `K_0 = 0`, `K_{r+1} = ℛ(λ K_r + (−P))`, where `−P = max` of `negP`. -/
def KData : ℕ → PolyFn m
  | 0 => PolyFn.const 0
  | r + 1 => PolyFn.rearrAll I.Δ (PolyFn.add (PolyFn.smul I.lam (KData r)) negP)

/-- `K_N` as data. -/
def KNData : PolyFn m := I.KData negP I.Nfix

/-- `F_0 = K_N − P` and `F_j = R_{j} F_{j−1}` (coordinates `0, …, m−1`); `Fseq j = F_j`. -/
def Fseq : ℕ → PolyFn m
  | 0 => PolyFn.add (I.KNData negP) negP
  | j + 1 => if h : j < m then PolyFn.rearr I.Δ ⟨j, h⟩ (Fseq j) else Fseq j

/-- Realisation error per coordinate. -/
def errStep : ℝ := I.d / (8 * (m + 1))

/-- The generator realising `R_{j}` on `F_{j}` (coordinate `j`, 0-based). -/
def stageGen (j : Fin m) : ℝ → Fibre m → ℝ :=
  realiseGen I.Δ (I.Fseq negP j) j (I.errStep)

/-- Stages in running order: coordinate `m−1` first, coordinate `0` last, so that
`q = q^{(0)} ∘ ⋯ ∘ q^{(m−1)}`. -/
def stages : List (ℝ → Fibre m → ℝ) := ((List.finRange m).map (I.stageGen negP)).reverse

/-- **The explicit comparison datum** of thm:cmp-main. -/
def comparatorDatum : ComparisonDatum m where
  K := lse (lseScale (I.KNData negP) (I.d / 32)) (I.KNData negP)
  Q := concatGen (I.stages negP)
  reserve := 11 * I.d / 64

/-- `KData` computes the iterates `Kiter` on `Δ`. -/
theorem KData_ne_nil (hneg : negP ≠ []) (r : ℕ) : I.KData negP r ≠ [] := by
  induction r with
  | zero => exact PolyFn.const_ne_nil 0
  | succ r ih =>
    exact PolyFn.rearrAll_ne_nil (PolyFn.add_ne_nil (PolyFn.smul_ne_nil ih _) hneg)

theorem KData_eval (hI : I.Spec) (hneg : negP ≠ [])
    (hP : ∀ p ∈ I.Δ.set, I.P p = -PolyFn.eval negP p) (r : ℕ) :
    EqOn (PolyFn.eval (I.KData negP r)) (I.Kiter r) I.Δ.set := by
  induction r with
  | zero => intro p _; exact PolyFn.eval_const 0 p
  | succ r ih =>
    have hK := I.KData_ne_nil negP hneg r
    have hl : 0 ≤ I.lam := (lt_trans (by norm_num) (lam_mem hI).1).le
    have hA := PolyFn.add_ne_nil (PolyFn.smul_ne_nil hK I.lam) hneg
    refine (PolyFn.rearrAll_eval hI.Δ_spec hA).trans ?_
    refine rearrAll_congr hI.Δ_spec fun p hp => ?_
    change PolyFn.eval (PolyFn.add (PolyFn.smul I.lam (I.KData negP r)) negP) p =
      I.lam * I.Kiter r p - I.P p
    rw [PolyFn.eval_add (PolyFn.smul_ne_nil hK _) hneg, PolyFn.eval_smul hl, ih hp, hP p hp]
    ring

/-! ### Telescoping (proof of thm:cmp-main) -/

theorem KNData_ne_nil (hneg : negP ≠ []) : I.KNData negP ≠ [] := I.KData_ne_nil negP hneg _

theorem Fseq_ne_nil (hneg : negP ≠ []) (j : ℕ) : I.Fseq negP j ≠ [] := by
  induction j with
  | zero => exact PolyFn.add_ne_nil (I.KNData_ne_nil negP hneg) hneg
  | succ j ih =>
    by_cases h : j < m
    · simp only [Fseq, dif_pos h]; exact PolyFn.rearr_ne_nil _ ih
    · simp only [Fseq, dif_neg h]; exact ih

theorem Fseq_succ {j : ℕ} (h : j < m) :
    I.Fseq negP (j + 1) = PolyFn.rearr I.Δ ⟨j, h⟩ (I.Fseq negP j) := by
  simp only [Fseq, dif_pos h]

/-- `F_s` is the data rearrangement along the first `s` coordinates. -/
theorem Fseq_eq_take {s : ℕ} (hs : s ≤ m) :
    I.Fseq negP s = ((List.finRange m).take s).foldl (fun G j => PolyFn.rearr I.Δ j G)
      (I.Fseq negP 0) := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h : s < m := hs
    have hl : s < (List.finRange m).length := by simpa using h
    rw [I.Fseq_succ negP h, ih h.le, List.take_succ, List.getElem?_eq_getElem hl]
    simp [List.foldl_append]

theorem Fseq_m_eq : I.Fseq negP m = PolyFn.rearrAll I.Δ (I.Fseq negP 0) := by
  rw [I.Fseq_eq_take negP le_rfl]
  have : (List.finRange m).take m = List.finRange m :=
    List.take_of_length_le (by simp)
  rw [this]; rfl

theorem errStep_pos (hI : I.Spec) : 0 < I.errStep := by
  unfold errStep
  have := hI.d_pos
  positivity

theorem stageGen_spec (hI : I.Spec) (hneg : negP ≠ []) (j : Fin m) :
    GenSpec (I.stageGen negP j) ∧ PreservesRegion I.Δ (I.stageGen negP j) ∧
      FaceCollar I.Δ (I.stageGen negP j) ∧
      ∀ w ∈ planeRegion I.Δ.b I.Δ.ℓ,
        PolyFn.eval (I.Fseq negP j) (planeMoments (isoOf (I.stageGen negP j) 1 w)) ≤
          rearr I.Δ j (PolyFn.eval (I.Fseq negP j)) (planeMoments w) + I.errStep :=
  realiseGen_spec hI.Δ_spec (I.Fseq_ne_nil negP hneg j) j (I.errStep_pos hI)

theorem mem_stages {Q : ℝ → Fibre m → ℝ} (hQ : Q ∈ I.stages negP) :
    ∃ j, Q = I.stageGen negP j := by
  unfold stages at hQ
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hQ)
  exact ⟨j, rfl⟩

/-- The partial composition `q^{(n)} ∘ ⋯ ∘ q^{(m−1)}`. -/
def partialMap (n : ℕ) (w : Fibre m) : Fibre m :=
  ((List.finRange m).drop n).foldr (fun j x => isoOf (I.stageGen negP j) 1 x) w

theorem qMap_eq (hI : I.Spec) (hneg : negP ≠ []) (w : Fibre m) :
    (I.comparatorDatum negP).qMap w = I.partialMap negP 0 w := by
  have hgen : ∀ Q ∈ I.stages negP, GenSpec Q := fun Q hQ => by
    obtain ⟨j, rfl⟩ := I.mem_stages negP hQ
    exact (I.stageGen_spec negP hI hneg j).1
  change isoOf (concatGen (I.stages negP)) 1 w = _
  rw [isoOf_concatGen_one hgen, stages, List.foldl_reverse, List.foldr_map]
  simp [partialMap]

/-- The telescoping estimate along the stages. -/
theorem partialMap_bound (hI : I.Spec) (hneg : negP ≠ []) {w : Fibre m}
    (hw : w ∈ planeRegion I.Δ.b I.Δ.ℓ) :
    ∀ k, k ≤ m → I.partialMap negP (m - k) w ∈ planeRegion I.Δ.b I.Δ.ℓ ∧
      PolyFn.eval (I.Fseq negP (m - k)) (planeMoments (I.partialMap negP (m - k) w)) ≤
        PolyFn.eval (I.Fseq negP m) (planeMoments w) + k * I.errStep := by
  intro k
  induction k with
  | zero =>
    intro _
    have hd : (List.finRange m).drop m = [] := List.drop_eq_nil_of_le (by simp)
    simp only [Nat.sub_zero, partialMap, hd, List.foldr_nil, CharP.cast_eq_zero, zero_mul,
      add_zero]
    exact ⟨hw, le_rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨hmem, hle⟩ := ih (by omega)
    set n := m - (k + 1) with hn
    have hn1 : m - k = n + 1 := by omega
    have hnm : n < m := by omega
    rw [hn1] at hmem hle
    have hl : n < (List.finRange m).length := by simpa using hnm
    have hstep : I.partialMap negP n w =
        isoOf (I.stageGen negP ⟨n, hnm⟩) 1 (I.partialMap negP (n + 1) w) := by
      simp only [partialMap]
      rw [List.drop_eq_getElem_cons hl]
      simp
    obtain ⟨-, hpres, -, hbd⟩ := I.stageGen_spec negP hI hneg ⟨n, hnm⟩
    rw [hstep]
    refine ⟨hpres 1 _ hmem, ?_⟩
    have h1 := hbd _ hmem
    have h2 := PolyFn.rearr_eval hI.Δ_spec ⟨n, hnm⟩ (I.Fseq_ne_nil negP hneg n)
      (show planeMoments (I.partialMap negP (n + 1) w) ∈ I.Δ.set from hmem)
    rw [← h2, ← I.Fseq_succ negP hnm] at h1
    push_cast
    linarith

/-- **thm:cmp-main.** -/
theorem comparatorDatum_spec (hI : I.Spec) (hneg : negP ≠ [])
    (hP : ∀ p ∈ I.Δ.set, I.P p = -PolyFn.eval negP p) :
    (I.comparatorDatum negP).Spec I.Δ I.P (11 * I.d / 16) := by
  have hΔ := hI.Δ_spec
  have hd := hI.d_pos
  have hKN := I.KNData_ne_nil negP hneg
  have hgen : ∀ Q ∈ I.stages negP, GenSpec Q := fun Q hQ => by
    obtain ⟨j, rfl⟩ := I.mem_stages negP hQ
    exact (I.stageGen_spec negP hI hneg j).1
  have hc : 0 < lseScale (I.KNData negP) (I.d / 32) := by
    unfold lseScale; exact_mod_cast Nat.succ_pos _
  refine ⟨lse_smooth _ hKN, concatGen_spec hgen, concatGen_preserves hgen ?_,
    concatGen_collar hgen ?_, by positivity, ?_,
    by change 0 < 11 * I.d / 64; positivity,
    by change 11 * I.d / 64 ≤ 11 * I.d / 16; linarith⟩
  · intro Q hQ
    obtain ⟨j, rfl⟩ := I.mem_stages negP hQ
    exact (I.stageGen_spec negP hI hneg j).2.1
  · intro Q hQ
    obtain ⟨j, rfl⟩ := I.mem_stages negP hQ
    exact (I.stageGen_spec negP hI hneg j).2.2.1
  intro w hw
  rw [I.qMap_eq negP hI hneg w]
  obtain ⟨hmem, hle⟩ := I.partialMap_bound negP hI hneg hw m le_rfl
  rw [Nat.sub_self] at hmem hle
  set x := I.partialMap negP 0 w
  have hx : planeMoments x ∈ I.Δ.set := hmem
  have hwΔ : planeMoments w ∈ I.Δ.set := hw
  -- `F_0 = K_N − P` on `Δ`
  have hF0 : EqOn (PolyFn.eval (I.Fseq negP 0)) (fun p => I.Kfin p - I.P p) I.Δ.set := by
    intro p hp
    change PolyFn.eval (PolyFn.add (I.KNData negP) negP) p = _
    rw [PolyFn.eval_add hKN hneg]
    show _ = I.Kfin p - I.P p
    rw [hP p hp]
    have := I.KData_eval negP hI hneg hP I.Nfix hp
    change PolyFn.eval (I.KNData negP) p = I.Kfin p at this
    rw [this]; ring
  -- `F_m = ℛ(K_N − P) ≤ K_N − 7d/8` on `Δ`
  have hFm : PolyFn.eval (I.Fseq negP m) (planeMoments w) ≤
      I.Kfin (planeMoments w) - 7 * I.d / 8 := by
    rw [I.Fseq_m_eq negP, PolyFn.rearrAll_eval hΔ (I.Fseq_ne_nil negP hneg 0) hwΔ,
      rearrAll_congr hΔ hF0 hwΔ]
    exact Kfin_gap hI _ hwΔ
  have hKNeq : ∀ p ∈ I.Δ.set, PolyFn.eval (I.KNData negP) p = I.Kfin p :=
    fun p hp => I.KData_eval negP hI hneg hP I.Nfix hp
  -- `m e ≤ d/8`
  have hme : (m : ℝ) * I.errStep ≤ I.d / 8 := by
    unfold errStep
    have hm1 : (0 : ℝ) < m + 1 := by positivity
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hF0x := hF0 hx
  simp only at hF0x
  rw [hF0x] at hle
  have hup := lse_lseScale_le hKN (show 0 < I.d / 32 by positivity) (planeMoments x)
  have hlo := eval_le_lse hc hKN (planeMoments w)
  rw [hKNeq _ hx] at hup
  rw [hKNeq _ hwΔ] at hlo
  change lse _ _ (planeMoments x) - I.P (planeMoments x) ≤ lse _ _ (planeMoments w) - _
  linarith

end CmpInput

end SymplecticPacking.HighDim
