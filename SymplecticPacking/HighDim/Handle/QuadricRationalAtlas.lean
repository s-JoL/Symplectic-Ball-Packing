import SymplecticPacking.HighDim.Handle.QuadricRawBoxes

/-!
# A countable algebraic atlas of the quadric

A countable algebraic atlas: rational ordinary coordinates and finite branch centres.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Filter
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped Topology

def rationalComplex (q : ℚ × ℚ) : ℂ :=
  Complex.equivRealProdCLM.symm ((q.1 : ℝ), (q.2 : ℝ))

theorem rationalComplex_dense : DenseRange rationalComplex := by
  exact Complex.equivRealProdCLM.symm.toHomeomorph.surjective.denseRange.comp
    (Rat.denseRange_cast.prodMap Rat.denseRange_cast)
    Complex.equivRealProdCLM.symm.continuous

/-- The geometric condition that `c` is an ordinary centre whose chart contains `x`. -/
def ordinaryCentreCondition {m : ℕ} {a : Fin m → ℂ} (x c : locus a) : Prop :=
  (∀ j, c.val.2 j ≠ 0) ∧ x ∈ ordinaryLocalSource c

theorem ordinaryCentreCondition_open {m : ℕ} {a : Fin m → ℂ} (x : locus a) :
    IsOpen {c | ordinaryCentreCondition x c} := by
  apply isOpen_iff_mem_nhds.mpr
  intro c hc
  have hn : ∀ j, ∀ᶠ d : locus a in 𝓝 c, d.val.2 j ≠ 0 := by
    intro j
    exact (isOpen_ne_fun (by fun_prop) continuous_const).mem_nhds (hc.1 j)
  have ha : ∀ j, ∀ᶠ d : locus a in 𝓝 c,
      0 < (1+(x.val.1^2-d.val.1^2)/(d.val.2 j)^2 : ℂ).re := by
    intro j
    have hcont : ContinuousAt (fun d : locus a =>
        (1+(x.val.1^2-d.val.1^2)/(d.val.2 j)^2 : ℂ).re) c := by
      apply Complex.continuous_re.continuousAt.comp
      apply ContinuousAt.add continuousAt_const
      exact (continuousAt_const.sub ((by fun_prop : ContinuousAt (fun d : locus a => d.val.1) c).pow 2)).div
        ((by fun_prop : ContinuousAt (fun d : locus a => d.val.2 j) c).pow 2)
        (pow_ne_zero 2 (hc.1 j))
    exact hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds (hc.2.1 j))
  have hr : ∀ j, ∀ᶠ d : locus a in 𝓝 c, 0 < (x.val.2 j/d.val.2 j).re := by
    intro j
    have hcont : ContinuousAt (fun d : locus a => (x.val.2 j/d.val.2 j).re) c :=
      Complex.continuous_re.continuousAt.comp
        (continuousAt_const.div (by fun_prop) (hc.1 j))
    exact hcont.preimage_mem_nhds (isOpen_Ioi.mem_nhds (hc.2.2 j))
  filter_upwards [Filter.eventually_all.mpr hn, Filter.eventually_all.mpr ha,
    Filter.eventually_all.mpr hr] with d hdn hda hdr
  exact ⟨hdn, hda, hdr⟩

theorem ordinaryCentreCondition_self {m : ℕ} {a : Fin m → ℂ} (x : locus a)
    (hx : ∀ j, x.val.2 j ≠ 0) : ordinaryCentreCondition x x :=
  ⟨hx, ordinaryExplicitChart_center x hx⟩

theorem branchPresentationCenter_complete {m : ℕ} {a : Fin m → ℂ} (x : locus a)
    (i : Fin m) (hi : x.val.2 i = 0) :
    ∃ ε₀ : Bool, ∃ ε : Fin m → Bool, branchPresentationCenter a i ε₀ ε = x := by
  have h0 : x.val.1^2 = a i := by
    have he := mem_locus.mp x.property i
    rw [hi, zero_pow (by decide)] at he
    exact sub_eq_zero.mp he.symm
  obtain ⟨ε₀, hε₀⟩ := signedRoot_complete h0
  have hh (j : Fin m) : ∃ ε : Bool, signedRoot ε (a i-a j) = x.val.2 j := by
    apply signedRoot_complete
    rw [mem_locus.mp x.property j, h0]
  choose ε hε using hh
  refine ⟨ε₀, ε, ?_⟩
  apply Subtype.ext
  apply Prod.ext hε₀
  funext j
  change (if j=i then 0 else signedRoot (ε j) (a i-a j)) = x.val.2 j
  by_cases hji : j=i
  · subst j
    simp only [ite_true, hi]
  · rw [ite_eq_right hji]
    exact hε j

end SymplecticPacking.HighDim.ToricPackingStages
