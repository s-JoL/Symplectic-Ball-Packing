import SymplecticPacking.General.Ham.Linear.Path
import SymplecticPacking.General.Ham.Linear.Bridge
import SymplecticPacking.General.Ham.Isotopy.Shape
import SymplecticPacking.Tail

/-!
# Parameters of the common isotopy

Hypotheses on the input (`IsoInput`): maps `f_i`, start centres `s_i` and per-ball radii
`0 < r₁ᵢ < r₂ᵢ < r₃ᵢ < r₄ᵢ < ρᵢ`, with `f_i` smooth and symplectic on `B(ρᵢ)`, injective on
`B̄(r₄ᵢ)` with pairwise disjoint images, and source clearance `r₃ᵢ + r₃ⱼ < |sᵢ - sⱼ|`.

Explicit parameters defined from them: `cᵢ = fᵢ(0)`, `Aᵢ = Dfᵢ(0)`, the linear paths
`M_{i,σ} = spPath(Aᵢ)(σ)`, the bound `L`, `r_Σ = 1 + Σ r₃ᵢ`, half the minimal distance of the
`cᵢ`, the common tail parameter `τ = min(1/2, δ_c / (2 L r_Σ))` and the far centres `Cᵢ = cᵢ / τ`,
`4 L r_Σ`-separated.
-/

noncomputable section

namespace SymplecticPacking.General.Ham.Isotopy

open Metric Set Finset Problem Linear
open scoped ContDiff

variable {n k : ℕ}

/-- Hypotheses on the input of the isotopy construction. -/
structure IsoInput (f : Fin k → E n → E n) (s : Fin k → E n) (r1 r2 r3 r4 ρ : Fin k → ℝ) :
    Prop where
  one_le_n : 1 ≤ n
  radii : ∀ i, 0 < r1 i ∧ r1 i < r2 i ∧ r2 i < r3 i ∧ r3 i < r4 i ∧ r4 i < ρ i
  smooth : ∀ i, ContDiffOn ℝ ∞ (f i) (ball 0 (ρ i))
  sympl : ∀ i, ∀ u ∈ ball (0 : E n) (ρ i), IsSymplecticLinear (fderiv ℝ (f i) u)
  inj : ∀ i, InjOn (f i) (closedBall 0 (r4 i))
  disj : ∀ i j, i ≠ j → Disjoint (f i '' closedBall 0 (r4 i)) (f j '' closedBall 0 (r4 j))
  sep : ∀ i j, i ≠ j → r3 i + r3 j < dist (s i) (s j)

/-- Centres `cᵢ = fᵢ(0)`. -/
def cen (f : Fin k → E n → E n) (i : Fin k) : E n := f i 0
/-- Linear parts `Aᵢ = Dfᵢ(0)`. -/
def lin (f : Fin k → E n → E n) (i : Fin k) : E n →L[ℝ] E n := fderiv ℝ (f i) 0
/-- The explicit linear paths `M_{i,σ}` from `1` to `Aᵢ`. -/
def linPath (f : Fin k → E n → E n) (i : Fin k) (σ : ℝ) : E n →L[ℝ] E n :=
  toCLM (spPath (ofCLM (lin f i)) σ)

/-- `L = 1 + Σᵢ (sup_{B̄(r₃ᵢ)} ‖Dfᵢ‖ + sup_{[0,1] × B̄(r₃ᵢ)} ‖M_{i,σ} u‖)`. -/
def bigL (f : Fin k → E n → E n) (r3 : Fin k → ℝ) : ℝ :=
  1 + ∑ i, (sSup ((fun y => ‖fderiv ℝ (f i) y‖) '' closedBall 0 (r3 i)) +
    sSup ((fun p : ℝ × E n => ‖linPath f i p.1 p.2‖) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ closedBall 0 (r3 i))))

/-- `r_Σ = 1 + Σᵢ r₃ᵢ`. -/
def rsum (r3 : Fin k → ℝ) : ℝ := 1 + ∑ i, r3 i

open scoped Classical in
/-- Half the minimal distance between the centres `cᵢ` (`1` if `k ≤ 1`). -/
def deltaC (f : Fin k → E n → E n) : ℝ :=
  if h : (univ : Finset (Fin k)).offDiag.Nonempty then
    (univ.offDiag.inf' h fun p => dist (cen f p.1) (cen f p.2)) / 2
  else 1

/-- `τ = min(1/2, δ_c / (2 L r_Σ))`. -/
def tau (f : Fin k → E n → E n) (r3 : Fin k → ℝ) : ℝ :=
  min (1 / 2) (deltaC f / (2 * bigL f r3 * rsum r3))

/-- Far centres `Cᵢ = cᵢ / τ`. -/
def farC (f : Fin k → E n → E n) (r3 : Fin k → ℝ) (i : Fin k) : E n := (tau f r3)⁻¹ • cen f i

variable {f : Fin k → E n → E n} {s : Fin k → E n} {r1 r2 r3 r4 ρ : Fin k → ℝ}

lemma IsoInput.r3_pos (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) : 0 < r3 i := by
  obtain ⟨h1, h2, h3, -⟩ := hf.radii i; linarith

lemma IsoInput.rsum_pos (hf : IsoInput f s r1 r2 r3 r4 ρ) : 1 ≤ rsum r3 := by
  have : 0 ≤ ∑ i, r3 i := Finset.sum_nonneg fun i _ => (hf.r3_pos i).le
  unfold rsum; linarith

lemma IsoInput.r3_le_rsum (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) : r3 i ≤ rsum r3 := by
  have := Finset.single_le_sum (f := r3) (fun j _ => (hf.r3_pos j).le) (Finset.mem_univ i)
  unfold rsum; linarith

lemma IsoInput.r3_add_r3_lt (hf : IsoInput f s r1 r2 r3 r4 ρ) {i j : Fin k} (hij : i ≠ j) :
    r3 i + r3 j < rsum r3 := by
  have h := Finset.sum_le_sum_of_subset_of_nonneg (f := r3)
    (show ({i, j} : Finset (Fin k)) ⊆ univ from Finset.subset_univ _)
    (fun l _ _ => (hf.r3_pos l).le)
  rw [Finset.sum_pair hij] at h
  unfold rsum; linarith

lemma IsoInput.lin_sympl (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) :
    IsSymplecticLinear (lin f i) :=
  hf.sympl i 0 (mem_ball_self (by obtain ⟨h1, h2, h3, h4, h5⟩ := hf.radii i; linarith))

lemma IsoInput.ofCLM_mem (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) :
    ofCLM (lin f i) ∈ Sp n :=
  Linear.ofCLM_mem (hf.lin_sympl i)

lemma linPath_zero (i : Fin k) : linPath f i 0 = ContinuousLinearMap.id ℝ (E n) := by
  rw [linPath, spPath_zero, toCLM_one]

lemma IsoInput.linPath_one (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) :
    linPath f i 1 = lin f i := by
  rw [linPath, spPath_one (hf.ofCLM_mem i), toCLM_ofCLM]

lemma IsoInput.linPath_sympl (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) (σ : ℝ) :
    IsSymplecticLinear (linPath f i σ) :=
  toCLM_isSymplectic (spPath_mem (hf.ofCLM_mem i) σ)

lemma IsoInput.contDiff_linPath_apply (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) :
    ContDiff ℝ ∞ (fun p : ℝ × E n => linPath f i p.1 p.2) :=
  contDiff_toCLM_apply (smoothEntries_spPath (hf.ofCLM_mem i))

/-! ### Bounds -/

lemma IsoInput.bdd_fderiv (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) :
    BddAbove ((fun y => ‖fderiv ℝ (f i) y‖) '' closedBall 0 (r3 i)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hf.radii i
  have hc : ContinuousOn (fderiv ℝ (f i)) (ball 0 (ρ i)) :=
    (hf.smooth i).continuousOn_fderiv_of_isOpen isOpen_ball (by simp)
  exact (isCompact_closedBall 0 (r3 i)).bddAbove_image
    ((hc.mono (closedBall_subset_ball (by linarith))).norm)

lemma IsoInput.bdd_linPath (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) :
    BddAbove ((fun p : ℝ × E n => ‖linPath f i p.1 p.2‖) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ closedBall 0 (r3 i))) :=
  (isCompact_Icc.prod (isCompact_closedBall 0 (r3 i))).bddAbove_image
    (hf.contDiff_linPath_apply i).continuous.norm.continuousOn

lemma sSup_image_nonneg {X : Type*} {S : Set X} (hs : S.Nonempty) {g : X → ℝ}
    (hg : ∀ x, 0 ≤ g x) (hb : BddAbove (g '' S)) : 0 ≤ sSup (g '' S) := by
  obtain ⟨x, hx⟩ := hs
  exact (hg x).trans (le_csSup hb ⟨x, hx, rfl⟩)

lemma IsoInput.one_le_L (hf : IsoInput f s r1 r2 r3 r4 ρ) : 1 ≤ bigL f r3 := by
  have hnn : ∀ l, 0 ≤ sSup ((fun y => ‖fderiv ℝ (f l) y‖) '' closedBall 0 (r3 l)) +
      sSup ((fun p : ℝ × E n => ‖linPath f l p.1 p.2‖) ''
        (Set.Icc (0 : ℝ) 1 ×ˢ closedBall 0 (r3 l))) := fun l =>
    add_nonneg
      (sSup_image_nonneg ⟨0, mem_closedBall_self (hf.r3_pos l).le⟩ (fun _ => norm_nonneg _)
        (hf.bdd_fderiv l))
      (sSup_image_nonneg (by exact ⟨((0 : ℝ), (0 : E n)), ⟨Set.left_mem_Icc.mpr zero_le_one,
          mem_closedBall_self (hf.r3_pos l).le⟩⟩)
        (fun _ => norm_nonneg _) (hf.bdd_linPath l))
  unfold bigL
  linarith [Finset.sum_nonneg fun l (_ : l ∈ Finset.univ) => hnn l]

lemma IsoInput.norm_fderiv_le (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) {y : E n}
    (hy : y ∈ closedBall (0 : E n) (r3 i)) : ‖fderiv ℝ (f i) y‖ ≤ bigL f r3 := by
  have hnn : ∀ l, 0 ≤ sSup ((fun y => ‖fderiv ℝ (f l) y‖) '' closedBall 0 (r3 l)) +
      sSup ((fun p : ℝ × E n => ‖linPath f l p.1 p.2‖) ''
        (Set.Icc (0 : ℝ) 1 ×ˢ closedBall 0 (r3 l))) := fun l =>
    add_nonneg
      (sSup_image_nonneg ⟨0, mem_closedBall_self (hf.r3_pos l).le⟩ (fun _ => norm_nonneg _)
        (hf.bdd_fderiv l))
      (sSup_image_nonneg (by exact ⟨((0 : ℝ), (0 : E n)), ⟨Set.left_mem_Icc.mpr zero_le_one,
          mem_closedBall_self (hf.r3_pos l).le⟩⟩)
        (fun _ => norm_nonneg _) (hf.bdd_linPath l))
  have h1 : ‖fderiv ℝ (f i) y‖ ≤ sSup ((fun y => ‖fderiv ℝ (f i) y‖) '' closedBall 0 (r3 i)) :=
    le_csSup (hf.bdd_fderiv i) ⟨y, hy, rfl⟩
  have h2 := sSup_image_nonneg (by exact ⟨((0 : ℝ), (0 : E n)), ⟨Set.left_mem_Icc.mpr zero_le_one,
      mem_closedBall_self (hf.r3_pos i).le⟩⟩) (fun _ => norm_nonneg _) (hf.bdd_linPath i)
  have h3 := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => hnn l) (Finset.mem_univ i)
  unfold bigL
  linarith

lemma IsoInput.norm_linPath_le (hf : IsoInput f s r1 r2 r3 r4 ρ) (i : Fin k) {σ : ℝ}
    (hσ : σ ∈ Set.Icc (0 : ℝ) 1) {u : E n} (hu : u ∈ closedBall (0 : E n) (r3 i)) :
    ‖linPath f i σ u‖ ≤ bigL f r3 := by
  have hnn : ∀ l, 0 ≤ sSup ((fun y => ‖fderiv ℝ (f l) y‖) '' closedBall 0 (r3 l)) +
      sSup ((fun p : ℝ × E n => ‖linPath f l p.1 p.2‖) ''
        (Set.Icc (0 : ℝ) 1 ×ˢ closedBall 0 (r3 l))) := fun l =>
    add_nonneg
      (sSup_image_nonneg ⟨0, mem_closedBall_self (hf.r3_pos l).le⟩ (fun _ => norm_nonneg _)
        (hf.bdd_fderiv l))
      (sSup_image_nonneg (by exact ⟨((0 : ℝ), (0 : E n)), ⟨Set.left_mem_Icc.mpr zero_le_one,
          mem_closedBall_self (hf.r3_pos l).le⟩⟩)
        (fun _ => norm_nonneg _) (hf.bdd_linPath l))
  have h1 : ‖linPath f i σ u‖ ≤ sSup ((fun p : ℝ × E n => ‖linPath f i p.1 p.2‖) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ closedBall 0 (r3 i))) :=
    le_csSup (hf.bdd_linPath i) ⟨(σ, u), ⟨hσ, hu⟩, rfl⟩
  have h2 := sSup_image_nonneg ⟨0, mem_closedBall_self (hf.r3_pos i).le⟩
    (fun _ => norm_nonneg _) (hf.bdd_fderiv i)
  have h3 := Finset.single_le_sum (fun l (_ : l ∈ Finset.univ) => hnn l) (Finset.mem_univ i)
  unfold bigL
  linarith

/-! ### Centres -/

lemma IsoInput.cen_ne (hf : IsoInput f s r1 r2 r3 r4 ρ) {i j : Fin k} (hij : i ≠ j) :
    cen f i ≠ cen f j := by
  have h0 : ∀ l, (0 : E n) ∈ closedBall (0 : E n) (r4 l) := fun l => mem_closedBall_self (by
    obtain ⟨h1, h2, h3, h4, -⟩ := hf.radii l; linarith)
  intro h
  exact Set.disjoint_left.mp (hf.disj i j hij) ⟨0, h0 i, rfl⟩ ⟨0, h0 j, h.symm⟩

lemma IsoInput.deltaC_pos (hf : IsoInput f s r1 r2 r3 r4 ρ) : 0 < deltaC f := by
  unfold deltaC
  split_ifs with h
  · apply half_pos
    rw [Finset.lt_inf'_iff]
    rintro ⟨i, j⟩ hp
    rw [Finset.mem_offDiag] at hp
    exact dist_pos.mpr (hf.cen_ne hp.2.2)
  · exact one_pos

lemma IsoInput.two_deltaC_le (hf : IsoInput f s r1 r2 r3 r4 ρ) {i j : Fin k} (hij : i ≠ j) :
    2 * deltaC f ≤ dist (cen f i) (cen f j) := by
  have hne : (univ : Finset (Fin k)).offDiag.Nonempty :=
    ⟨(i, j), show (i, j) ∈ (univ : Finset (Fin k)).offDiag from
      Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hij⟩⟩
  unfold deltaC
  rw [dif_pos hne]
  have := Finset.inf'_le (fun p : Fin k × Fin k => dist (cen f p.1) (cen f p.2))
    (show (i, j) ∈ (univ : Finset (Fin k)).offDiag from
      Finset.mem_offDiag.mpr ⟨Finset.mem_univ i, Finset.mem_univ j, hij⟩)
  linarith

lemma IsoInput.tau_pos (hf : IsoInput f s r1 r2 r3 r4 ρ) : 0 < tau f r3 :=
  lt_min (by norm_num) (div_pos hf.deltaC_pos
    (mul_pos (mul_pos two_pos (by linarith [hf.one_le_L])) (by linarith [hf.rsum_pos])))

lemma tau_le_half : tau f r3 ≤ 1 / 2 := min_le_left _ _

/-- `|Cᵢ - Cⱼ| ≥ 4 L r_Σ` for `i ≠ j`. -/
lemma IsoInput.farC_sep (hf : IsoInput f s r1 r2 r3 r4 ρ) {i j : Fin k} (hij : i ≠ j) :
    4 * bigL f r3 * rsum r3 ≤ dist (farC f r3 i) (farC f r3 j) := by
  have hτ := hf.tau_pos
  have hL := hf.one_le_L
  have hr := hf.rsum_pos
  have hd := hf.two_deltaC_le hij
  have hτ' : tau f r3 ≤ deltaC f / (2 * bigL f r3 * rsum r3) := min_le_right _ _
  rw [farC, farC, dist_smul₀, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hτ)]
  rw [le_div_iff₀ (by positivity)] at hτ'
  rw [le_inv_mul_iff₀ hτ]
  nlinarith

end SymplecticPacking.General.Ham.Isotopy
