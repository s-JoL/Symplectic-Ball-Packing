import SymplecticPacking.BranchLarge3.ExactFibreCore
import SymplecticPacking.Return.Flow

/-!
# Step S4a: the explicit radial bridge `Ξ`

The radial bridge from the physical coordinates `BaseCurve × ℂ²` to the disk coordinates of the
cubic cone: `Ξ(x, z) = (x, χ(ζ) · R_{a(x)}⁻¹(ζ))`, where `ζ = physicalDiskCoordinates L z`,
`R_a⁻¹` is the inverse radial disk map (`diskInverse latticeIndex a`, with the quadrant inverse
of the moment map written as the definite description of the unique nonnegative preimage) with
weights
`a(x) = coefficientSquares (cubicCoefficients D S x)`, and `χ` is an explicit smooth cutoff in
the two squared radii, equal to `1` at margin `≥ δ` inside the disk domain and `0` at margin
`≤ δ/2`. The margin `δ` is half the minimum over `K` of the distance (in squared radii) to the
boundary of the disk domain.

Paper: supplement `six-return.tex` (radial bridge).
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3

open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.FiniteMoment
open OAI.PackingSufficiencySupport.FiniteMoment.Radial
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set Filter

namespace CubicBridge

/-- Distance (in squared radii) of `z` from the boundary of `diskDomain A B`. -/
def margin (A B : ℕ) (z : DiskPair) : ℝ :=
  min ((A : ℝ) - (squaredRadii z).1) ((B : ℝ) - (squaredRadii z).1 - (squaredRadii z).2)

theorem margin_continuous (A B : ℕ) : Continuous (margin A B) := by
  unfold margin
  have h := squaredRadii_contDiff.continuous
  exact (continuous_const.sub h.fst).min ((continuous_const.sub h.fst).sub h.snd)

theorem margin_pos_iff {A B : ℕ} {z : DiskPair} : 0 < margin A B z ↔ z ∈ diskDomain A B := by
  unfold margin diskDomain
  simp only [lt_min_iff, mem_setOf_eq, sub_pos]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩

/-- The minimal margin over `K`. -/
def minMargin (A B : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace) : ℝ :=
  sInf ((fun p : CubicPhysicalSpace => margin A B (physicalDiskCoordinates L p.2)) '' K)

/-- The cutoff margin `δ > 0`. -/
def delta (A B : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace) : ℝ :=
  if 0 < minMargin A B L K then minMargin A B L K / 2 else 1

theorem delta_pos (A B : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace) : 0 < delta A B L K := by
  unfold delta; split_ifs with h
  · positivity
  · norm_num

/-- The smooth cutoff in the squared radii. -/
def cut (A B : ℕ) (δ : ℝ) (z : DiskPair) : ℝ :=
  Return.step (δ / 2) δ ((A : ℝ) - (squaredRadii z).1) *
    Return.step (δ / 2) δ ((B : ℝ) - (squaredRadii z).1 - (squaredRadii z).2)

theorem cut_contDiff (A B : ℕ) (δ : ℝ) : ContDiff ℝ ∞ (cut A B δ) := by
  unfold cut
  have h := squaredRadii_contDiff
  exact ((Return.step_contDiff _ _).comp (contDiff_const.sub h.fst)).mul
    ((Return.step_contDiff _ _).comp ((contDiff_const.sub h.fst).sub h.snd))

theorem cut_eq_one {A B : ℕ} {δ : ℝ} (hδ : 0 < δ) {z : DiskPair} (hz : δ < margin A B z) :
    cut A B δ z = 1 := by
  unfold margin at hz
  rw [lt_min_iff] at hz
  unfold cut
  rw [Return.step_eq_one (by linarith) hz.1.le, Return.step_eq_one (by linarith) hz.2.le, one_mul]

/-- The weights `a(x)`. -/
def weights (A B D S : ℕ) (x : BaseCurve) : TrapezoidWeight A B → ℝ :=
  coefficientSquares (cubicCoefficients (A := A) (B := B) D S x)

theorem weights_pos (A B D S : ℕ) (x : BaseCurve) (i : TrapezoidWeight A B) :
    0 < weights A B D S x i := by
  unfold weights
  rw [cubicCoefficients_squares]
  exact coefficientNorm_pos _ _ _

open Classical in
/-- The inverse of the radial moment map on the closed quadrant, as a definite description
(the unique nonnegative preimage; `0` if there is none). -/
def expInv (A B : ℕ) (a : TrapezoidWeight A B → ℝ) (p : Radial.Plane) : Radial.Plane :=
  if h : ∃! r : Radial.Plane, (0 ≤ r.1 ∧ 0 ≤ r.2) ∧ Radial.moment latticeIndex a r = p then
    Explicit.the h else 0

theorem expInv_eq {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) {a : TrapezoidWeight A B → ℝ}
    (ha : ∀ i, 0 < a i) {p : Radial.Plane} (hp : p ∈ lowerTrapezoid A B) :
    expInv A B a p = nonnegativeInverse latticeIndex a p := by
  have hex := trapezoid_radial_surjective hAB ha hp
  have hP : (0 ≤ (nonnegativeInverse latticeIndex a p).1 ∧
      0 ≤ (nonnegativeInverse latticeIndex a p).2) ∧
      Radial.moment latticeIndex a (nonnegativeInverse latticeIndex a p) = p :=
    ⟨nonnegativeInverse_nonneg _ _ _, nonnegativeInverse_spec hex⟩
  have hu : ∃! r : Radial.Plane, (0 ≤ r.1 ∧ 0 ≤ r.2) ∧ Radial.moment latticeIndex a r = p :=
    ⟨_, hP, fun r hr => moment_injective_quadrant ha (lattice_zero A B)
      (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB) hr.1 hP.1 (hr.2.trans hP.2.symm)⟩
  rw [expInv, dif_pos hu]
  exact Explicit.the_eq hu hP

/-- The inverse radial disk map, with the explicit quadrant inverse `expInv`. -/
def diskInv (A B : ℕ) (a : TrapezoidWeight A B → ℝ) (z : DiskPair) : DiskPair :=
  ((Real.sqrt (Radial.slope latticeIndex a (expInv A B a (squaredRadii z))).1)⁻¹ • z.1,
   (Real.sqrt (Radial.slope latticeIndex a (expInv A B a (squaredRadii z))).2)⁻¹ • z.2)

theorem diskInv_eq {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) {a : TrapezoidWeight A B → ℝ}
    (ha : ∀ i, 0 < a i) {z : DiskPair} (hz : z ∈ diskDomain A B) :
    diskInv A B a z = diskInverse latticeIndex a z := by
  unfold diskInv diskInverse
  rw [expInv_eq hA hAB ha (squaredRadii_mem_lower hz)]

/-- The fibre part of the bridge, on `(weights, disk point)`. -/
def fibre (A B : ℕ) (δ : ℝ) (q : (TrapezoidWeight A B → ℝ) × DiskPair) : DiskPair :=
  cut A B δ q.2 • diskInv A B q.1 q.2

theorem fibre_contDiffAt {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) {δ : ℝ} (hδ : 0 < δ)
    {q : (TrapezoidWeight A B → ℝ) × DiskPair} (hq : ∀ i, 0 < q.1 i) :
    ContDiffAt ℝ ∞ (fibre A B δ) q := by
  by_cases hz : q.2 ∈ diskDomain A B
  · have hO : IsOpen {r : (TrapezoidWeight A B → ℝ) × DiskPair |
        (∀ i, 0 < r.1 i) ∧ r.2 ∈ diskDomain A B} :=
      positiveCoefficients_isOpen.prod (diskDomain_isOpen A B)
    apply (((cut_contDiff A B δ).comp contDiff_snd).contDiffAt.smul
      (diskInverse_contDiffAt hA hAB hq hz)).congr_of_eventuallyEq
    filter_upwards [hO.mem_nhds ⟨hq, hz⟩] with r hr
    simp only [fibre, diskInv_eq hA hAB hr.1 hr.2]
    rfl
  · apply Return.contDiffAt_of_eventually_zero
    have hm : margin A B q.2 ≤ 0 := not_lt.mp (fun h => hz (margin_pos_iff.mp h))
    have hev : ∀ᶠ r in 𝓝 q, margin A B r.2 < δ / 2 :=
      ((margin_continuous A B).comp continuous_snd).continuousAt.eventually_lt
        continuousAt_const (by change margin A B q.2 < δ / 2; linarith)
    filter_upwards [hev] with r hr
    have hc : cut A B δ r.2 = 0 := by
      unfold margin at hr
      unfold cut
      rcases min_lt_iff.mp hr with h | h
      · rw [Return.step_eq_zero (by linarith) h.le, zero_mul]
      · rw [Return.step_eq_zero (by linarith) h.le, mul_zero]
    simp only [fibre, hc, zero_smul, Pi.zero_apply]

end CubicBridge

open CubicBridge

/-- The explicit radial bridge `Ξ`. -/
def bridgeMap (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace) :
    CubicPhysicalSpace → BaseCurve × DiskPair := fun p =>
  (p.1, fibre A B (delta A B L K) (weights A B D S p.1, physicalDiskCoordinates L p.2))

/-- The explicit open domain of the bridge. -/
def bridgeDomain (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace) : Set CubicPhysicalSpace :=
  {p | delta A B L K < margin A B (physicalDiskCoordinates L p.2)}

theorem bridge_spec {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B) (D S : ℕ) {L : ℝ} (hL : 0 < L)
    {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    (hKd : ∀ p ∈ K, physicalDiskCoordinates L p.2 ∈ diskDomain A B) :
    let Ξ := bridgeMap A B D S L K
    let V := bridgeDomain A B D S L K
    ContMDiff 𝓘(ℝ, RealModel × PlanePhase (Fin 2)) 𝓘(ℝ, RealModel × DiskPair) ∞ Ξ ∧
      (∀ p, (Ξ p).1 = p.1) ∧ IsOpen V ∧ K ⊆ V ∧
      (∀ p ∈ V, physicalDiskCoordinates L p.2 ∈ diskDomain A B) ∧
      Topology.IsEmbedding (fun p : V => Ξ p.val) ∧
      ∀ p ∈ V, (Ξ p).2 = diskInverse latticeIndex
        (coefficientSquares (cubicCoefficients (A := A) (B := B) D S p.1))
        (physicalDiskCoordinates L p.2) := by
  intro Ξ V
  set δ := delta A B L K with hδdef
  have hδ : 0 < δ := delta_pos A B L K
  let a : BaseCurve → TrapezoidWeight A B → ℝ := weights A B D S
  have ha : ContMDiff 𝓘(ℝ, RealModel) 𝓘(ℝ, TrapezoidWeight A B → ℝ) ∞ a :=
    coefficientSquares_contDiff.contMDiff.comp (cubicCoefficients_smooth D S)
  let F : CubicPhysicalSpace → (TrapezoidWeight A B → ℝ) × DiskPair :=
    fun p => (a p.1, physicalDiskCoordinates L p.2)
  have hF : ContMDiff 𝓘(ℝ, RealModel × PlanePhase (Fin 2))
      𝓘(ℝ, (TrapezoidWeight A B → ℝ) × DiskPair) ∞ F :=
    (ha.comp (flatProduct_fst_smooth (V := PlanePhase (Fin 2)))).prodMk_space
      ((physicalDiskCoordinates L).contDiff.contMDiff.comp
        (flatProduct_snd_smooth (E := RealModel) (M := BaseCurve)))
  have hG : ContMDiff 𝓘(ℝ, RealModel × PlanePhase (Fin 2)) 𝓘(ℝ, DiskPair) ∞
      (fun p : CubicPhysicalSpace => fibre A B δ (F p)) := by
    intro p
    exact (fibre_contDiffAt hA hAB hδ (weights_pos A B D S p.1)).contMDiffAt.comp p
      hF.contMDiffAt
  have hΞ : ContMDiff 𝓘(ℝ, RealModel × PlanePhase (Fin 2)) 𝓘(ℝ, RealModel × DiskPair) ∞ Ξ := by
    rw [show 𝓘(ℝ, RealModel × DiskPair) = (𝓘(ℝ, RealModel)).prod 𝓘(ℝ, DiskPair) from
      modelWithCornersSelf_prod]
    exact (flatProduct_fst_smooth (E := RealModel) (M := BaseCurve)
      (V := PlanePhase (Fin 2))).prodMk hG
  have hV : IsOpen V :=
    isOpen_lt continuous_const
      ((margin_continuous A B).comp ((physicalDiskCoordinates L).continuous.comp continuous_snd))
  have hVd : ∀ p ∈ V, physicalDiskCoordinates L p.2 ∈ diskDomain A B := fun p hp =>
    margin_pos_iff.mp (lt_trans hδ hp)
  have he : ∀ p ∈ V, (Ξ p).2 = diskInverse latticeIndex
      (coefficientSquares (cubicCoefficients (A := A) (B := B) D S p.1))
      (physicalDiskCoordinates L p.2) := by
    intro p hp
    change cut A B δ (physicalDiskCoordinates L p.2) •
      diskInv A B (weights A B D S p.1) (physicalDiskCoordinates L p.2) = _
    rw [cut_eq_one hδ hp, one_smul, diskInv_eq hA hAB (weights_pos A B D S p.1) (hVd p hp)]
    rfl
  refine ⟨hΞ, fun _ => rfl, hV, ?_, hVd, ?_, he⟩
  · intro p hp
    have hne : K.Nonempty := ⟨p, hp⟩
    let m : CubicPhysicalSpace → ℝ := fun q => margin A B (physicalDiskCoordinates L q.2)
    have hm : Continuous m :=
      (margin_continuous A B).comp ((physicalDiskCoordinates L).continuous.comp continuous_snd)
    have himg : IsCompact (m '' K) := hK.image hm
    obtain ⟨q, hq, hqe⟩ := himg.sInf_mem (hne.image m)
    have hμ : minMargin A B L K = m q := hqe.symm
    have hμpos : 0 < minMargin A B L K := by
      rw [hμ]; exact margin_pos_iff.mpr (hKd q hq)
    have hle : minMargin A B L K ≤ m p := csInf_le himg.bddBelow (mem_image_of_mem m hp)
    change δ < m p
    rw [hδdef, delta, if_pos hμpos]
    linarith
  · let R : BaseCurve × DiskPair → CubicPhysicalSpace :=
      fun p => (p.1, CubicModel.physicalDiskRecovery L (diskForward latticeIndex (a p.1) p.2))
    have hforward : ContMDiff 𝓘(ℝ, RealModel × DiskPair) 𝓘(ℝ, DiskPair) ∞
        (fun p : BaseCurve × DiskPair => diskForward latticeIndex (a p.1) p.2) := by
      have hp := (ha.comp (flatProduct_fst_smooth (V := DiskPair))).prodMk_space
        (flatProduct_snd_smooth (E := RealModel) (M := BaseCurve) (V := DiskPair))
      intro p
      exact (diskForward_contDiffAt (weights_pos A B D S p.1) (lattice_zero A B)
        (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB) p.2).contMDiffAt.comp p
          hp.contMDiffAt
    have hR : Continuous R := continuous_fst.prodMk
      ((CubicModel.physicalDiskRecovery_smooth L).continuous.comp hforward.continuous)
    have hRI (p : CubicPhysicalSpace) (hp : p ∈ V) : R (Ξ p) = p := by
      change (p.1, CubicModel.physicalDiskRecovery L
        (diskForward latticeIndex (a p.1) (Ξ p).2)) = p
      rw [show (Ξ p).2 = diskInverse latticeIndex (a p.1) (physicalDiskCoordinates L p.2) from
        he p hp, diskForward_inverse (weights_pos A B D S p.1) (lattice_zero A B)
        (lattice_unit_fst hA hAB) (lattice_unit_snd hA hAB)
        (trapezoid_radial_surjective hAB (weights_pos A B D S p.1)
          (squaredRadii_mem_lower (hVd p hp))),
        CubicModel.physicalDiskRecovery_left hL]
    apply Topology.IsEmbedding.of_comp (hΞ.continuous.comp continuous_subtype_val) hR
    have he' : R ∘ (fun p : V => Ξ p.val) = Subtype.val :=
      funext fun p => hRI p.val p.property
    change Topology.IsEmbedding (R ∘ (fun p : V => Ξ p.val))
    rw [he']
    exact Topology.IsEmbedding.subtypeVal

end SymplecticPacking.BranchLarge3
