import SymplecticPacking.BranchSmall.TransportClock
import SymplecticPacking.BranchSmall.FlowReflection

/-!
# Complete positive-time horizontal transport
-/

noncomputable section
namespace SymplecticPacking.BranchSmall.VT
open Set Filter Topology ContinuousLinearMap
open SymplecticPacking.Return (CSField flow)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff
variable {q : ℕ}

theorem graphTube_eq_of_graph (a : Fin q → ℂ) {t : ℝ} (ht : t ≠ 0) (y : Tot q)
    (hy : equations a y.1 = (t : ℂ) • y.2) : graphTube a t y.1 = y := by
  apply Prod.ext
  · rfl
  · change (t : ℂ)⁻¹ • equations a y.1 = y.2
    rw [hy, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr ht), one_smul]

theorem goodSet_of_zero_pattern {y z : Tot q}
    (h : ∀ i : Option (Fin q), affineComplex q y.1 i = 0 ↔ affineComplex q z.1 i = 0)
    (hz : z ∈ goodSet q) : y ∈ goodSet q := by
  have h0 : y.1.1 = 0 ↔ z.1.1 = 0 := h none
  have hj (j : Fin q) : y.1.2 j = 0 ↔ z.1.2 j = 0 := h (some j)
  constructor
  · rcases hz.1 with hz0 | hzs
    · exact Or.inl (fun hy0 => hz0 (h0.mp hy0))
    · exact Or.inr (fun j hyj => hzs j ((hj j).mp hyj))
  · intro i j hij
    rcases hz.2 i j hij with hzi | hzj
    · exact Or.inl (fun hyi => hzi ((hj i).mp hyi))
    · exact Or.inr (fun hyj => hzj ((hj j).mp hyj))

/-- A complete positive segment from an arbitrary regular graph point. -/
theorem exists_positive_transport_segment (a : Fin q → ℂ) {b δ : ℝ}
    (hb0 : 0 < b) (hb : b < 1 / 2) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (y : Tot q) (hy : y ∈ goodSet q) (hgraph : equations a y.1 = (δ : ℂ) • y.2) :
    ∃ γ : ℝ → Tot q, γ δ = y ∧ ∀ t ∈ Icc δ (1 : ℝ),
      γ t ∈ goodSet q ∧ HasDerivAt γ (transportField a b t (γ t)) t := by
  obtain ⟨W, O, hW, hO, hVW, hstay⟩ := logarithmicTransport_control a hb0.le hb δ y.1
  let β : ℝ → Affine q := fun s => flow W s y.1
  have hβ0 : β 0 = y.1 := hW.flow_zero _
  have hβ (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      HasDerivAt β (logarithmicTransport a b δ s (β s)) s := by
    rw [hVW s hs _ (hstay s hs)]
    exact hW.flow_hasDerivAt y.1 s
  have hβzero (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (i : Option (Fin q)) :
      affineComplex q (β s) i = 0 ↔ affineComplex q y.1 i = 0 := by
    rw [← affineReflection_fixed, ← affineReflection_fixed, ← hβ0]
    exact trajectory_reflection_fixed_iff (logarithmicTransport_contDiff a hb0.le hb δ)
      (affineReflection i) (affineReflection_involutive i) (affineReflection_norm i)
      (fun s z => logarithmicTransport_reflection a hb0.le hb δ s i z)
      (fun s hs => (hβ s hs).hasDerivWithinAt) s hs
  let z : ℝ → Affine q := fun t => β (transportClockInverse δ t)
  let γ : ℝ → Tot q := fun t => graphTube a t (z t)
  have hγδ : γ δ = y := by
    change graphTube a δ (β (transportClockInverse δ δ)) = y
    rw [transportClockInverse_self, hβ0]
    exact graphTube_eq_of_graph a hδ0.ne' y hgraph
  refine ⟨γ, hγδ, ?_⟩
  intro t ht
  have ht0 : 0 < t := hδ0.trans_le ht.1
  have hS := transportClockInverse_mem hδ0 hδ1 ht
  have hT := transportClock_inverse hδ0 hδ1 ht0
  have hlog : Real.log δ ≠ 0 := (Real.log_neg hδ0 hδ1).ne
  have hz : HasDerivAt z ((-(radialCoefficient (γ t) / t)) • normalReturnField a b t (z t)) t := by
    have hh := (hβ _ hS).scomp t (transportClockInverse_hasDerivAt (δ := δ) ht0.ne')
    change HasDerivAt z _ t at hh
    convert! hh using 1
    simp only [logarithmicTransport, hT, smul_smul]
    congr 1
    field_simp [hlog, ht0.ne']
    ring
  have hF := ((equations_hasFDerivAt a (z t)).restrictScalars ℝ).comp_hasDerivAt t hz
  have hI := (hasDerivAt_inv (𝕜 := ℝ) ht0.ne').ofReal_comp
  simp only [Complex.ofReal_inv] at hI
  have hγ' := hz.prodMk (hI.smul hF)
  change HasDerivAt γ _ t at hγ'
  have hγd : DifferentiableAt ℝ γ t := hγ'.differentiableAt
  have hγgraph : ∀ᶠ s in 𝓝 t, equations a (γ s).1 = (s : ℂ) • (γ s).2 := by
    filter_upwards [(isOpen_ne.mem_nhds ht0.ne')] with s hs
    change equations a (z s) = (s : ℂ) • ((s : ℂ)⁻¹ • equations a (z s))
    rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hs), one_smul]
  have hbase : (deriv γ t).1 = (transportField a b t (γ t)).1 := by
    have h1 := (ContinuousLinearMap.fst ℝ (Affine q) (Fin q → ℂ)).hasFDerivAt.comp_hasDerivAt t hγd.hasDerivAt
    change HasDerivAt (fun s => (γ s).1) (deriv γ t).1 t at h1
    have he : (fun s => (γ s).1) = z := rfl
    rw [he] at h1
    have hh := h1.unique hz
    rw [transportField_graphTube_base a hb0 hb ht0.ne']
    exact hh
  have hvel := transport_velocity_of_graph a hb0 hb ht0.ne' hγd.hasDerivAt hγgraph hbase
  refine ⟨goodSet_of_zero_pattern (fun i => hβzero _ hS i) hy, ?_⟩
  simpa only [hvel] using hγd.hasDerivAt

end SymplecticPacking.BranchSmall.VT
