import SymplecticPacking.HighDim.Comparator.PlanarGenSpecCore

/-!
# The active parameter cutoff stays inside the uniform coefficient envelope
-/

noncomputable section
namespace SymplecticPacking.HighDim.PlanarGen
open Set Filter Topology
open scoped ContDiff
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)

variable {m q : ℕ}

/-- Smooth face data give the globally smooth parameter cutoff. -/
theorem paramCut_smooth {Δ : Polytope m q} {j : Fin m}
    {Lν : Fin q → Moments m → ℝ} {R η₀ : ℝ}
    (hLν : ∀ ν, ContDiff ℝ ∞ (Lν ν)) : ContDiff ℝ ∞ (paramCut Δ j Lν R η₀) := by
  unfold paramCut
  apply ContDiff.mul
  · apply contDiff_prod
    intro i _
    exact Real.smoothTransition.contDiff.comp
      ((contDiff_const.sub ((contDiff_apply ℝ ℝ i).pow 2)).div_const _)
  · apply contDiff_prod
    intro ν _
    by_cases hν : 0 < Δ.b ν j
    · simp only [if_pos hν]
      exact Real.smoothTransition.contDiff.comp (((hLν ν).sub contDiff_const).div_const _)
    · simp only [if_neg hν]
      exact contDiff_const

/-- A smooth coefficient cutoff extends a smooth family from a neighbourhood of its closed
support, including the rescaling of time by the same coefficient. -/
theorem cutoff_rescaled_family_smooth {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {χ : P → ℝ} {U : Set P} {B : P → ℝ → ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hU : IsOpen U) (hs : tsupport χ ⊆ U)
    (hB : ContDiffOn ℝ ∞ (fun q : (P × ℝ) × ℂ => B q.1.1 q.1.2 q.2)
      ((U ×ˢ univ) ×ˢ univ)) :
    ContDiff ℝ ∞ (fun q : P × ℝ × ℂ => χ q.1 * B q.1 (χ q.1 * q.2.1) q.2.2) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x.1 ∈ tsupport χ
  · have hχx : ContDiff ℝ ∞ (fun q : P × ℝ × ℂ => χ q.1) := hχ.comp contDiff_fst
    have ht : ContDiff ℝ ∞ (fun q : P × ℝ × ℂ => χ q.1 * q.2.1) :=
      hχx.mul (contDiff_fst.comp contDiff_snd)
    have hmap : ContDiff ℝ ∞ (fun q : P × ℝ × ℂ => ((q.1, χ q.1 * q.2.1), q.2.2)) :=
      (contDiff_fst.prodMk ht).prodMk (contDiff_snd.comp contDiff_snd)
    have hb : ContDiffAt ℝ ∞ (fun q : (P × ℝ) × ℂ => B q.1.1 q.1.2 q.2)
        ((x.1, χ x.1 * x.2.1), x.2.2) :=
      hB.contDiffAt (((hU.prod isOpen_univ).prod isOpen_univ).mem_nhds
        ⟨⟨hs hx, mem_univ _⟩, mem_univ _⟩)
    have hc : ContDiffAt ℝ ∞ (fun q : P × ℝ × ℂ => B q.1 (χ q.1 * q.2.1) q.2.2) x :=
      ContDiffAt.comp x
        (g := fun q : (P × ℝ) × ℂ => B q.1.1 q.1.2 q.2)
        (f := fun q : P × ℝ × ℂ => ((q.1, χ q.1 * q.2.1), q.2.2)) hb hmap.contDiffAt
    exact hχx.contDiffAt.mul hc
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    have hn : ∀ᶠ q in 𝓝 (x : P × ℝ × ℂ), q.1 ∉ tsupport χ :=
      (continuous_fst.tendsto x).eventually ((isClosed_tsupport χ).isOpen_compl.mem_nhds hx)
    filter_upwards [hn] with q hq
    have hz : χ q.1 = 0 := by
      by_contra hz
      exact hq (subset_tsupport χ hz)
    rw [hz, zero_mul]

/-- Nonzero cutoff implies the strict box and slice-length inequalities. -/
theorem paramCut_ne_zero_bounds {Δ : Polytope m q} {j : Fin m}
    {Lν : Fin q → Moments m → ℝ} {R η₀ : ℝ} {y : Moments m}
    (hR : 0 < R) (hη : 0 < η₀) (hy : paramCut Δ j Lν R η₀ y ≠ 0) :
    (∀ i, |y i| < 4 * R) ∧ (∀ ν, 0 < Δ.b ν j → η₀ / 2 < Lν ν y) := by
  have hp := mul_ne_zero_iff.mp hy
  constructor
  · intro i
    have ht : Real.smoothTransition ((16 * R ^ 2 - y i ^ 2) / (7 * R ^ 2)) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hp.1) i (Finset.mem_univ i)
    have harg : 0 < (16 * R ^ 2 - y i ^ 2) / (7 * R ^ 2) := by
      by_contra hc
      exact ht (Real.smoothTransition.zero_of_nonpos (not_lt.mp hc))
    have hmul := (div_pos_iff.mp harg).resolve_right (by intro hc; linarith [sq_nonneg R])
    have hs := hmul.1
    rw [abs_lt]
    constructor <;> nlinarith [hR]
  · intro ν hν
    have ht := (Finset.prod_ne_zero_iff.mp hp.2) ν (Finset.mem_univ ν)
    rw [if_pos hν] at ht
    have harg : 0 < (Lν ν y - η₀ / 2) / (η₀ / 4) := by
      by_contra hc
      exact ht (Real.smoothTransition.zero_of_nonpos (not_lt.mp hc))
    have hh := (lt_div_iff₀ (by positivity : 0 < η₀ / 4)).mp harg
    linarith

/-- The closed cutoff support remains inside the closed box and positive face margins. -/
theorem paramCut_tsupport_bounds {Δ : Polytope m q} {j : Fin m}
    {Lν : Fin q → Moments m → ℝ} {R η₀ : ℝ} {y : Moments m}
    (hR : 0 < R) (hη : 0 < η₀) (hLν : ∀ ν, Continuous (Lν ν))
    (hy : y ∈ tsupport (paramCut Δ j Lν R η₀)) :
    (∀ i, |y i| ≤ 4 * R) ∧ (∀ ν, 0 < Δ.b ν j → η₀ / 2 ≤ Lν ν y) := by
  constructor
  · intro i
    have hcl : IsClosed {p : Moments m | |p i| ≤ 4 * R} :=
      isClosed_le (continuous_apply i |>.abs) continuous_const
    have hh : closure (Function.support (paramCut Δ j Lν R η₀)) ⊆
        {p : Moments m | |p i| ≤ 4 * R} := by
      apply closure_minimal _ hcl
      intro p hp
      exact ((paramCut_ne_zero_bounds hR hη hp).1 i).le
    exact hh hy
  · intro ν hν
    have hcl : IsClosed {p : Moments m | η₀ / 2 ≤ Lν ν p} :=
      isClosed_le continuous_const (hLν ν)
    have hh : closure (Function.support (paramCut Δ j Lν R η₀)) ⊆
        {p : Moments m | η₀ / 2 ≤ Lν ν p} := by
      apply closure_minimal _ hcl
      intro p hp
      exact ((paramCut_ne_zero_bounds hR hη hp).2 ν hν).le
    exact hh hy


theorem faceTerm_le_lenBound4 (Δ : Polytope m q) (j : Fin m) {R : ℝ} (hR : 0 < R)
    {y : Moments m} (hy : ∀ i, |y i| ≤ 4 * R) {μ : Fin q} (hμ : 0 < Δ.b μ j) :
    (Δ.ℓ μ - ∑ i, (if i = j then 0 else Δ.b μ i * y i)) / Δ.b μ j ≤ lenBound Δ j R - 1 := by
  have hnum : Δ.ℓ μ - ∑ i, (if i = j then 0 else Δ.b μ i * y i) ≤
      |Δ.ℓ μ| + 4 * R * ∑ i, |Δ.b μ i| := by
    have h1 : -(∑ i, (if i = j then 0 else Δ.b μ i * y i)) ≤ 4 * R * ∑ i, |Δ.b μ i| := by
      rw [← Finset.sum_neg_distrib, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      split_ifs
      · rw [neg_zero]; exact mul_nonneg (by linarith) (abs_nonneg _)
      · have hyi := hy i
        have h2 : -(Δ.b μ i * y i) ≤ |Δ.b μ i| * |y i| := by
          rw [← abs_mul]; exact neg_le_abs _
        have h3 : |Δ.b μ i| * |y i| ≤ |Δ.b μ i| * (4 * R) :=
          mul_le_mul_of_nonneg_left hyi (abs_nonneg _)
        nlinarith [abs_nonneg (Δ.b μ i)]
    linarith [le_abs_self (Δ.ℓ μ)]
  have hterm := div_le_div_of_nonneg_right hnum hμ.le
  have hsum : (|Δ.ℓ μ| + 4 * R * ∑ i, |Δ.b μ i|) / Δ.b μ j ≤
      ∑ ν, (if 0 < Δ.b ν j then (|Δ.ℓ ν| + 4 * R * ∑ i, |Δ.b ν i|) / Δ.b ν j else 0) := by
    have := Finset.single_le_sum
      (f := fun ν => if 0 < Δ.b ν j then (|Δ.ℓ ν| + 4 * R * ∑ i, |Δ.b ν i|) / Δ.b ν j else 0)
      (fun ν _ => by
        split_ifs with h
        · exact div_nonneg (add_nonneg (abs_nonneg _)
            (mul_nonneg (by linarith) (Finset.sum_nonneg fun i _ => abs_nonneg _))) h.le
        · exact le_rfl) (Finset.mem_univ μ)
    simpa only [hμ, if_true] using this
  unfold lenBound
  linarith


end SymplecticPacking.HighDim.PlanarGen
