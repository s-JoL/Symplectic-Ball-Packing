import SymplecticPacking.BranchLargeHigh.Params
import SymplecticPacking.BranchLargeHigh.Scaling
import SymplecticPacking.BranchLargeHigh.SecondStage
import SymplecticPacking.BranchLargeHigh.ShellDeriv

/-!
# Branch n ≥ 4, one c_j ≥ C/2 (quadric curve, slit shell, two-stage closed base)

`embeddings` and `embeddings_spec` are the interface used by `SymplecticPacking.General.Main`.
The definition is total (it does not take the hypotheses); `embeddings_spec` states its
properties under the branch hypotheses.

Paper `thm:lrg-high`, supplement `thm:two-packing`. In normalised units (`def:ham-normalise`):

* the large ball (`C ≤ 2 c_i`; at most one) is embedded by the identity into the reserved central
  ball `B(a)`, `a = A + t` (`Params.lean`);
* every small ball `i` is embedded by `shell_δ ∘ g_i`, where `g_i` are the second-stage maps into
  the first coupled line (`SecondStage.lean`) and `shell_δ` is the slit-shell map
  (`Shell.lean`) with `δ = min((1-h̄)(1-M̄), 1 - a - h̄)`; its image lies in the shell
  `a < π|y|² < 1`.

The physical maps are `scaleConj C` of these (`Scaling.lean`).
-/

noncomputable section

namespace SymplecticPacking.BranchLargeHigh

open Problem General Set
open scoped ContDiff

variable {k : ℕ}

/-- The second-stage maps for the small balls of `(m + 1, k, C, c)`. -/
def ssG (m k : ℕ) (C : ℝ) (c : Fin k → ℝ) : Small k C c → E (m + 1) → E (m + 1) :=
  secondStage m (aPar (m + 1) k C c) (fun i : Small k C c => rho C c i)
    (fun i : Small k C c => rPar (m + 1) k C c i)

/-- Their output capacities `ρ̂_i`. -/
def ssHat (m k : ℕ) (C : ℝ) (c : Fin k → ℝ) : Small k C c → ℝ :=
  secondStageHat m (aPar (m + 1) k C c) (fun i : Small k C c => rho C c i)
    (fun i : Small k C c => rPar (m + 1) k C c i)

/-- The fibre-moment bound `h̄`. -/
def ssH (m k : ℕ) (C : ℝ) (c : Fin k → ℝ) : ℝ :=
  secondStageH m (aPar (m + 1) k C c) (fun i : Small k C c => rho C c i)
    (fun i : Small k C c => rPar (m + 1) k C c i)

/-- The base-moment bound `M̄`. -/
def ssM (m k : ℕ) (C : ℝ) (c : Fin k → ℝ) : ℝ :=
  secondStageM m (aPar (m + 1) k C c) (fun i : Small k C c => rho C c i)
    (fun i : Small k C c => rPar (m + 1) k C c i)

/-- The slit parameter `δ = min((1 - h̄)(1 - M̄), 1 - a - h̄)`. -/
def deltaPar (m k : ℕ) (C : ℝ) (c : Fin k → ℝ) : ℝ :=
  min ((1 - ssH m k C c) * (1 - ssM m k C c)) (1 - aPar (m + 1) k C c - ssH m k C c)

/-- The normalised embedding of a small ball: `shell_δ ∘ g_i`. -/
def smallMap (m k : ℕ) (C : ℝ) (c : Fin k → ℝ) (i : Small k C c) (y : E (m + 1)) :
    E (m + 1) :=
  shell (deltaPar m k C c) (ssG m k C c i y)

/-- The embedding data in dimension `m + 1`. -/
def embeddingsAux (m k : ℕ) (C : ℝ) (c : Fin k → ℝ) : EmbeddingData (m + 1) k where
  f i := if h : C ≤ 2 * c i then id else scaleConj C (smallMap m k C c ⟨i, h⟩)
  enlarged i := if h : C ≤ 2 * c i then C * (rho C c i + tInc (m + 1) k C c / 2)
    else C * ((rho C c i + ssHat m k C c ⟨i, h⟩) / 2)
  domain i := if h : C ≤ 2 * c i then C * (rho C c i + tInc (m + 1) k C c)
    else C * ssHat m k C c ⟨i, h⟩

/-- The explicit enlarged-source embeddings of the branch. -/
def embeddings (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) : EmbeddingData n k :=
  match n with
  | 0 => ⟨fun _ => id, fun _ => 0, fun _ => 0⟩
  | m + 1 => embeddingsAux m k C c

lemma isOpen_capBallOpen {n : ℕ} (d : ℝ) : IsOpen (capBallOpen (0 : E n) d) :=
  isOpen_lt (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2))
    continuous_const

lemma capBall_subset_open {n : ℕ} {e d : ℝ} (h : e < d) :
    capBall (0 : E n) e ⊆ capBallOpen 0 d := fun y hy => lt_of_le_of_lt hy h

section proof

variable {m : ℕ} {C : ℝ} {c : Fin k → ℝ} (hB : BranchHyp (m + 1) k C c) (hm : 3 ≤ m)
include hB hm

lemma ss_spec :
    SecondStageSpec m (aPar (m + 1) k C c) (fun i : Small k C c => rho C c i) (ssG m k C c)
      (ssHat m k C c) (ssH m k C c) (ssM m k C c) := by
  obtain ⟨j, hj⟩ := hB.large
  obtain ⟨ha, ha1, -, hr, hvol⟩ := aux_spec hB hj
  exact secondStage_spec hm ha ha1 (fun i => rho_pos hB i)
    (fun i => by simp only [rPar]; linarith [tInc_pos hB]) (fun i => hr i i.2) hvol

lemma deltaPar_pos : 0 < deltaPar m k C c := by
  have hS := ss_spec hB hm
  have hh := hS.h_lt
  have hM := hS.M_lt
  obtain ⟨j, hj⟩ := hB.large
  obtain ⟨ha, -, -, -, -⟩ := aux_spec hB hj
  unfold deltaPar
  exact lt_min (mul_pos (by linarith) (by linarith)) (by linarith)

/-- The second-stage image lies in the shell domain, and the small-ball image lies in the shell
`a < π|y|² < 1`. -/
lemma smallMap_mem (i : Small k C c) {y : E (m + 1)} (hy : y ∈ capBallOpen 0 (ssHat m k C c i)) :
    ssG m k C c i y ∈ shellDomain (deltaPar m k C c) ∧
      aPar (m + 1) k C c < Real.pi * ‖smallMap m k C c i y‖ ^ 2 ∧
      Real.pi * ‖smallMap m k C c i y‖ ^ 2 < 1 := by
  have hS := ss_spec hB hm
  have hδ := deltaPar_pos hB hm
  have hu := hS.fib_le i y hy
  have hμ := hS.base_le i y hy
  have hh := hS.h_lt
  have hM := hS.M_lt
  obtain ⟨j, hj⟩ := hB.large
  obtain ⟨ha, -, -, -, -⟩ := aux_spec hB hj
  have hd1 : deltaPar m k C c ≤ (1 - ssH m k C c) * (1 - ssM m k C c) := min_le_left _ _
  have hd2 : deltaPar m k C c ≤ 1 - aPar (m + 1) k C c - ssH m k C c := min_le_right _ _
  have hrad := radicand_pos_of_bounds hδ hM.le (by linarith) (by linarith) hu hμ
  have hu1 : fibMoment (ssG m k C c i y) < 1 := by linarith
  have hcap := shell_capacity (deltaPar m k C c) hu1.le hrad.le
  have hx0 := xs_pos hδ (ssG m k C c i y)
  have hx1 := xs_lt hδ (ssG m k C c i y)
  refine ⟨⟨hu1, hrad⟩, ?_, ?_⟩
  · rw [smallMap, hcap]; linarith
  · rw [smallMap, hcap]; linarith

lemma smallMap_contDiffOn (i : Small k C c) :
    ContDiffOn ℝ ∞ (smallMap m k C c i) (capBallOpen 0 (ssHat m k C c i)) := by
  have hS := ss_spec hB hm
  intro y hy
  exact (shell_contDiffAt (deltaPar_pos hB hm) (smallMap_mem hB hm i hy).1).comp_contDiffWithinAt
    y (hS.smooth i y hy)

lemma smallMap_sympl (i : Small k C c) {y : E (m + 1)} (hy : y ∈ capBallOpen 0 (ssHat m k C c i))
    (v w : E (m + 1)) :
    Problem.omega0 (fderiv ℝ (smallMap m k C c i) y v) (fderiv ℝ (smallMap m k C c i) y w) =
      Problem.omega0 v w := by
  have hS := ss_spec hB hm
  have hδ := deltaPar_pos hB hm
  have hmem := (smallMap_mem hB hm i hy).1
  have hg : DifferentiableAt ℝ (ssG m k C c i) y :=
    ((hS.smooth i).contDiffAt ((isOpen_capBallOpen _).mem_nhds hy)).differentiableAt
      (by simp)
  have hsh : DifferentiableAt ℝ (shell (deltaPar m k C c)) (ssG m k C c i y) :=
    (shell_contDiffAt hδ hmem).differentiableAt (by simp)
  have hcomp : fderiv ℝ (smallMap m k C c i) y =
      (fderiv ℝ (shell (deltaPar m k C c)) (ssG m k C c i y)).comp
        (fderiv ℝ (ssG m k C c i) y) := by
    have : smallMap m k C c i = shell (deltaPar m k C c) ∘ ssG m k C c i := rfl
    rw [this, fderiv_comp y hsh hg]
  rw [hcomp]
  simp only [ContinuousLinearMap.comp_apply]
  rw [shell_pullback hδ hmem]
  exact hS.coupled i y hy v w

lemma smallMap_injOn (i : Small k C c) :
    InjOn (smallMap m k C c i) (capBallOpen 0 (ssHat m k C c i)) := by
  have hS := ss_spec hB hm
  intro y hy y' hy' h
  exact hS.inj i hy hy' (shell_injOn (deltaPar_pos hB hm) (smallMap_mem hB hm i hy).1
    (smallMap_mem hB hm i hy').1 h)

lemma smallMap_disj {i i' : Small k C c} (hii : i ≠ i') :
    Disjoint (smallMap m k C c i '' capBallOpen 0 (ssHat m k C c i))
      (smallMap m k C c i' '' capBallOpen 0 (ssHat m k C c i')) := by
  have hS := ss_spec hB hm
  rw [Set.disjoint_left]
  rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', h⟩
  have := shell_injOn (deltaPar_pos hB hm) (smallMap_mem hB hm i' hy').1
    (smallMap_mem hB hm i hy).1 h
  exact Set.disjoint_left.1 (hS.disj i i' hii) ⟨y, hy, rfl⟩ ⟨y', hy', this⟩

end proof

/-- The embeddings of the branch satisfy the interface specification. -/
theorem embeddings_spec {n k : ℕ} {C : ℝ} {c : Fin k → ℝ}
    (hn : 4 ≤ n) (hk : 1 ≤ k) (hC : 0 < C) (hc : ∀ i, 0 < c i)
    (hpair : ∀ i j, i ≠ j → c i + c j < C) (hvol : ∑ i, c i ^ n < C ^ n)
    (hlarge : ∃ j, C ≤ 2 * c j) :
    EmbeddingSpec n k C c (embeddings n k C c) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 3 ≤ m := by omega
  have hB : BranchHyp (m + 1) k C c := ⟨by omega, hk, hC, hc, hpair, hvol, hlarge⟩
  have hS := ss_spec hB hm
  have ht := tInc_pos hB
  -- facts about a large index
  have hlg : ∀ i, C ≤ 2 * c i →
      rho C c i + tInc (m + 1) k C c = aPar (m + 1) k C c ∧ aPar (m + 1) k C c < 1 := by
    intro i hi
    obtain ⟨-, ha1, he, -, -⟩ := aux_spec hB hi
    exact ⟨he, ha1⟩
  have hρC : ∀ i, C * rho C c i = c i := fun i => by rw [rho]; field_simp
  change EmbeddingSpec (m + 1) k C c (embeddingsAux m k C c)
  -- the image of a large ball is in `{π|y|² < C a}`, that of a small ball in `{π|y|² > C a}`
  have hbig : ∀ i (h : C ≤ 2 * c i), ∀ z ∈ (embeddingsAux m k C c).f i ''
      capBall 0 ((embeddingsAux m k C c).enlarged i),
      Real.pi * ‖z‖ ^ 2 < C * aPar (m + 1) k C c := by
    intro i h z hz
    simp only [embeddingsAux, dif_pos h, image_id] at hz
    have hz' : Real.pi * ‖z‖ ^ 2 ≤ C * (rho C c i + tInc (m + 1) k C c / 2) := by
      simpa [capBall] using hz
    rw [← (hlg i h).1]
    nlinarith
  have hsmall : ∀ i (h : ¬ C ≤ 2 * c i), ∀ z ∈ (embeddingsAux m k C c).f i ''
      capBall 0 ((embeddingsAux m k C c).enlarged i),
      C * aPar (m + 1) k C c < Real.pi * ‖z‖ ^ 2 ∧ Real.pi * ‖z‖ ^ 2 < C := by
    intro i h z hz
    simp only [embeddingsAux, dif_neg h] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hy' := (mem_capBall_scale hC).1 hy
    have hyo : (Real.sqrt C)⁻¹ • y ∈ capBallOpen 0 (ssHat m k C c ⟨i, h⟩) :=
      capBall_subset_open (by linarith [hS.lt_hat ⟨i, h⟩]) hy'
    obtain ⟨-, h1, h2⟩ := smallMap_mem hB hm ⟨i, h⟩ hyo
    rw [scaleConj_cap hC]
    constructor
    · exact mul_lt_mul_of_pos_left h1 hC
    · nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- lt_enlarged
    intro i
    simp only [embeddingsAux]
    split_ifs with h
    · rw [← hρC i]; nlinarith
    · rw [← hρC i]; have := hS.lt_hat ⟨i, h⟩; nlinarith
  · -- enlarged_lt_domain
    intro i
    simp only [embeddingsAux]
    split_ifs with h
    · nlinarith
    · have := hS.lt_hat ⟨i, h⟩; nlinarith
  · -- smooth
    intro i
    simp only [embeddingsAux]
    split_ifs with h
    · exact contDiff_id.contDiffOn
    · exact scaleConj_contDiffOn hC (smallMap_contDiffOn hB hm ⟨i, h⟩)
  · -- symplectic
    intro i u hu
    simp only [embeddingsAux] at hu ⊢
    split_ifs at hu ⊢ with h
    · rw [fderiv_id]; intro v w; rfl
    · have hu' := (mem_capBallOpen_scale hC).1 hu
      have hd : DifferentiableAt ℝ (smallMap m k C c ⟨i, h⟩) ((Real.sqrt C)⁻¹ • u) :=
        ((smallMap_contDiffOn hB hm ⟨i, h⟩).contDiffAt
          ((isOpen_capBallOpen _).mem_nhds hu')).differentiableAt (by simp)
      exact scaleConj_sympl hC hd (smallMap_sympl hB hm ⟨i, h⟩ hu')
  · -- injective
    intro i
    simp only [embeddingsAux]
    split_ifs with h
    · exact injOn_id _
    · apply scaleConj_injOn hC
      exact (smallMap_injOn hB hm ⟨i, h⟩).mono
        (capBall_subset_open (by linarith [hS.lt_hat ⟨i, h⟩]))
  · -- disjoint
    intro i i' hii
    rw [Set.disjoint_left]
    intro z hz hz'
    by_cases h : C ≤ 2 * c i <;> by_cases h' : C ≤ 2 * c i'
    · exact hii (large_unique hB h h')
    · linarith [hbig i h z hz, (hsmall i' h' z hz').1]
    · linarith [hbig i' h' z hz', (hsmall i h z hz).1]
    · simp only [embeddingsAux, dif_neg h, dif_neg h'] at hz hz'
      rw [scaleConj_image hC] at hz hz'
      obtain ⟨p, hp, rfl⟩ := hz
      obtain ⟨p', hp', hpp⟩ := hz'
      have hs0 : Real.sqrt C ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hC)
      have hpe : p' = p := smul_right_injective _ hs0 hpp
      subst hpe
      have hne : (⟨i, h⟩ : Small k C c) ≠ ⟨i', h'⟩ := fun e => hii (congrArg Subtype.val e)
      have hsub : ∀ (j : Small k C c), smallMap m k C c j '' capBall 0 ((rho C c j + ssHat m k C c j) / 2)
          ⊆ smallMap m k C c j '' capBallOpen 0 (ssHat m k C c j) :=
        fun j => image_mono (capBall_subset_open (by linarith [hS.lt_hat j]))
      exact Set.disjoint_left.1 (smallMap_disj hB hm hne) (hsub _ hp) (hsub _ hp')
  · -- into
    intro i z hz
    by_cases h : C ≤ 2 * c i
    · have := hbig i h z hz
      have hlt := (hlg i h).2
      show Real.pi * ‖z - 0‖ ^ 2 < C
      rw [sub_zero]; nlinarith
    · have := (hsmall i h z hz).2
      show Real.pi * ‖z - 0‖ ^ 2 < C
      rw [sub_zero]; exact this

end SymplecticPacking.BranchLargeHigh
