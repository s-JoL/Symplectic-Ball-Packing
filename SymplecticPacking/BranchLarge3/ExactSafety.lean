import Mathlib
import SymplecticPacking.Explicit

/-!
# Derivative bounds for guards along a flow

Explicit compact derivative bounds for finitely many guards along a given global flow.
-/

noncomputable section
namespace SymplecticPacking.BranchLarge3.ExactSafety
open Set Function

variable {X : Type*} [TopologicalSpace X] {n : ℕ}

/-- The guard family is evaluated on the complete flow before this construction.
Only continuous extrema on the displayed compact sets enter these constants. -/
def initialValues (f : Fin n → ℝ × X → ℝ) (K : Set X) : Set ℝ :=
  insert 1 (⋃ i, (fun x => f i (0,x)) '' K)

def derivativeValues (f : Fin n → ℝ × X → ℝ) (K : Set X) : Set ℝ :=
  insert 0 (⋃ i, (fun p : ℝ × X => |deriv (fun s => f i (s,p.2)) p.1|) '' (Icc (-1) 1 ×ˢ K))

def clearance (f : Fin n → ℝ × X → ℝ) (K : Set X) : ℝ := sInf (initialValues f K)

def speed (f : Fin n → ℝ × X → ℝ) (K : Set X) : ℝ := 1+sSup (derivativeValues f K)

/-- The closed interval `[-τ,2τ]` is controlled, giving room at both ODE endpoints. -/
def time (f : Fin n → ℝ × X → ℝ) (K : Set X) (δ : ℝ) : ℝ :=
  min (min (δ/2) (1/4)) (clearance f K/(4*speed f K))

lemma initialValues_compact {f : Fin n → ℝ × X → ℝ} {K : Set X} (hK : IsCompact K)
    (hf : ∀ i,ContinuousOn (fun x => f i (0,x)) K) : IsCompact (initialValues f K) :=
  (isCompact_iUnion (fun i => hK.image_of_continuousOn (hf i))).insert 1

lemma derivativeValues_compact {f : Fin n → ℝ × X → ℝ} {K : Set X} (hK : IsCompact K)
    (hf : ∀ i,ContinuousOn (fun p : ℝ × X => deriv (fun s => f i (s,p.2)) p.1)
      (Icc (-1) 1 ×ˢ K)) : IsCompact (derivativeValues f K) :=
  (isCompact_iUnion (fun i => (isCompact_Icc.prod hK).image_of_continuousOn (hf i).abs)).insert 0

lemma clearance_pos {f : Fin n → ℝ × X → ℝ} {K : Set X} (hK : IsCompact K)
    (hf : ∀ i,ContinuousOn (fun x => f i (0,x)) K)
    (hpos : ∀ i,∀ x∈K,0<f i (0,x)) : 0<clearance f K := by
  have hc := initialValues_compact hK hf
  have hm := hc.sInf_mem (show (initialValues f K).Nonempty from ⟨1,mem_insert _ _⟩)
  rcases hm with hm | hm
  · change 0<sInf (initialValues f K)
    rw [hm]
    norm_num
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hm
    obtain ⟨x,hx,he⟩ := hi
    change 0 < sInf (initialValues f K)
    rw [← he]
    exact hpos i x hx

lemma clearance_le {f : Fin n → ℝ × X → ℝ} {K : Set X} (hK : IsCompact K)
    (hf : ∀ i,ContinuousOn (fun x => f i (0,x)) K) (i : Fin n) {x : X} (hx : x∈K) :
    clearance f K ≤ f i (0,x) :=
  csInf_le (initialValues_compact hK hf).bddBelow
    (mem_insert_of_mem _ (mem_iUnion.mpr ⟨i,x,hx,rfl⟩))

lemma speed_pos {f : Fin n → ℝ × X → ℝ} {K : Set X} (hK : IsCompact K)
    (hf : ∀ i,ContinuousOn (fun p : ℝ × X => deriv (fun s => f i (s,p.2)) p.1)
      (Icc (-1) 1 ×ˢ K)) : 0<speed f K := by
  have hz : (0 : ℝ) ≤ sSup (derivativeValues f K) :=
    le_csSup (derivativeValues_compact hK hf).bddAbove (mem_insert _ _)
  unfold speed
  linarith

lemma derivative_le {f : Fin n → ℝ × X → ℝ} {K : Set X} (hK : IsCompact K)
    (hf : ∀ i,ContinuousOn (fun p : ℝ × X => deriv (fun s => f i (s,p.2)) p.1)
      (Icc (-1) 1 ×ˢ K)) (i : Fin n) {x : X} (hx : x∈K) {s : ℝ} (hs : s∈Icc (-1) 1) :
    |deriv (fun r => f i (r,x)) s| ≤ speed f K := by
  have hh := le_csSup (derivativeValues_compact hK hf).bddAbove
    (mem_insert_of_mem 0 (mem_iUnion.mpr ⟨i,(s,x),⟨hs,hx⟩,rfl⟩))
  unfold speed
  linarith

lemma time_pos {f : Fin n → ℝ × X → ℝ} {K : Set X} {δ : ℝ}
    (hc : 0<clearance f K) (hv : 0<speed f K) (hδ : 0<δ) : 0<time f K δ := by
  unfold time
  exact lt_min (lt_min (by positivity) (by norm_num)) (by positivity)

lemma time_bounds (f : Fin n → ℝ × X → ℝ) (K : Set X) (δ : ℝ) :
    time f K δ ≤ δ/2 ∧ time f K δ ≤ 1/4 ∧ time f K δ ≤ clearance f K/(4*speed f K) :=
  ⟨(min_le_left _ _).trans (min_le_left _ _),
    (min_le_left _ _).trans (min_le_right _ _),min_le_right _ _⟩

/-- The scalar mean-value estimate gives strict positivity throughout the whole closed
flow enclosure. No existence assertion about local ODE trajectories is searched. -/
theorem guard_ge_half {f : Fin n → ℝ × X → ℝ} {K : Set X} {δ : ℝ}
    (hK : IsCompact K)
    (h0 : ∀ i,ContinuousOn (fun x => f i (0,x)) K)
    (hd : ∀ i,ContinuousOn (fun p : ℝ × X => deriv (fun s => f i (s,p.2)) p.1)
      (Icc (-1) 1 ×ˢ K))
    (hder : ∀ i,∀ x∈K,∀ s∈Icc (-1) 1,DifferentiableAt ℝ (fun r => f i (r,x)) s)
    (hpos : ∀ i,∀ x∈K,0<f i (0,x)) (hδ : 0<δ)
    (i : Fin n) {x : X} (hx : x∈K) {s : ℝ} (hs : |s|≤2*time f K δ) :
    clearance f K/2 ≤ f i (s,x) := by
  have hc := clearance_pos hK h0 hpos
  have hv := speed_pos hK hd
  have ht := time_pos hc hv hδ
  have hb := time_bounds f K δ
  have hsI : s∈Icc (-1) 1 := by
    rw [abs_le] at hs
    constructor <;> linarith [hs.1,hs.2]
  have he := (convex_Icc (-1:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr => (hder i x hx r hr).hasDerivAt.hasDerivWithinAt)
    (fun r hr => by simpa only [Real.norm_eq_abs] using derivative_le hK hd i hx hr)
    (show (0:ℝ)∈Icc (-1) 1 by norm_num) hsI
  have hdif : |f i (s,x)-f i (0,x)| ≤ speed f K*|s| := by
    simpa only [Real.norm_eq_abs,sub_zero] using he
  have hmul := mul_le_mul_of_nonneg_left hs hv.le
  have hbudget : speed f K*(2*time f K δ) ≤ clearance f K/2 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*speed f K)).mp hb.2.2
    nlinarith
  have hinit := clearance_le hK h0 i hx
  have hlo := (abs_le.mp hdif).1
  linarith

#check_explicit clearance
#check_explicit speed
#check_explicit time
end SymplecticPacking.BranchLarge3.ExactSafety
