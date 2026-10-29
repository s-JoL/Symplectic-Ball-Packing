import SymplecticPacking.Embed.Assemble
import SymplecticPacking.Branch2.Model.Cubic.Strip.Embed
import SymplecticPacking.Branch2.Model.Cubic.Handle.HandleMoserSpec

/-!
# The capacity-scale embeddings for valid cubic data (`prop:rtc-embeddings`)

`fcap P Φ⁻¹ i = b_ball ∘ 𝒯 ∘ Ncoord ∘ f_i^N` (`rem:shd-four`) with `f_i^N = Φ⁻¹ ∘ 𝒟⁻¹ ∘ E_i`
(`Strip.Cubic.fN`), on the source ball `𝔹_{ρ̂_i} = Strip.Cubic.srcBall P i`, for a Moser map
with `Strip.Cubic.PhiInvSpec P Φ Φ⁻¹` and `DeckEquivariant Φ⁻¹`. The return `𝒯`
(`Return.compositeT`) and the ball chart depend only on `d_n`, `h` and are those of `Return/*`
(smoothness lemmas in `Embed/Assemble.lean`).

* `prop:rtc-embeddings`: `contDiffAt_fcap`, `fcap_symplectic`, `fcap_injective`,
  `fcap_disjoint`, `fcap_mem_ball`;
* with the concrete handle Moser map `Handle.Cubic.handlePhiInv P`: `fcapV P i` and its
  specification `fcapV_smooth`, `fcapV_symplectic`, `fcapV_injective`, `fcapV_disjoint`,
  `fcapV_mem_ball`.
-/

noncomputable section

namespace SymplecticPacking.Embed.Cubic

open _root_.Complex ComplexConjugate Set Metric Filter Topology
open SymplecticPacking.Forms (Form2 pull2 pull2_apply)
open SymplecticPacking.Return (Ncoord C3 NDom compositeT compositeBall ballChart c2ToE4 nsq nsq2
  injection OmegaE)
open SymplecticPacking.Strip.Cubic (fN srcBall)
open scoped Real ContDiff

/-- **Capacity-scale embeddings** (`rem:shd-four`):
`f_i^cap = b_ball ∘ ψ₁⁻¹ ∘ pr ∘ τ₁ ∘ ι ∘ Ncoord ∘ f_i^N`. -/
def fcap (P : Branch2.VCubic) (PhiInv : E4 → E4) (i : ℕ) (X : E4) : E4 :=
  c2ToE4 (compositeBall P.dn P.h (Ncoord (fN P PhiInv i X)))

lemma dn_pos (P : Branch2.VCubic) : 0 < P.dn := P.h_pos.trans P.h_lt_dn

lemma OmegaT_zero_apply (P : Branch2.VCubic) (X a b : E4) :
    Bundle.Cubic.OmegaT P 0 X a b = Bundle.Omega0loc X a b := by
  simp only [Bundle.Cubic.OmegaT, add_apply, smul_apply,
    zero_smul, add_zero]

section cap

variable {P : Branch2.VCubic} {Phi PhiInv : E4 → E4} (hΦ : Strip.Cubic.PhiInvSpec P Phi PhiInv)
include hΦ

/-- The facts about `Q = f_i^N(X)` used below: `Ncoord Q ∈ N_{p ≤ h}`, `Q` is off the fibres
over `C ∩ L` (`Z₀ ≠ 0`), and `p(Q) < h`. -/
lemma fN_facts {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {X : E4} (hX : X ∈ srcBall P i) :
    Ncoord (fN P PhiInv i X) ∈ NDom P.h ∧ (Ncoord (fN P PhiInv i X)).1 0 ≠ 0 ∧
      Bundle.pE (fN P PhiInv i X) < P.h := by
  have hp := Strip.Cubic.fN_mem hΦ hi1 hik hX
  have hf := Strip.Cubic.fN_avoid_fibres hΦ hi1 hik hX
  refine ⟨⟨Return.nsq_Zunit _ _, Fpoly_Zunit _ _, ?_⟩, ?_, hp⟩
  · show Return.pN (((fN P PhiInv i X) 0 : ℂ) + ((fN P PhiInv i X) 1 : ℂ) * I) ≤ P.h
    rw [Return.pN_fibre]; exact hp.le
  · intro h0
    obtain ⟨j, m, n, hu, hv⟩ := (Bundle.Z0_eq_zero_iff _ _).mp h0
    exact hf ⟨j, m, n, hu, hv⟩

/-- `𝒯(Ncoord Q)` is a unit vector with `Z₀ ≠ 0`. -/
lemma compositeT_facts {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {X : E4} (hX : X ∈ srcBall P i) :
    nsq (compositeT P.dn P.h (Ncoord (fN P PhiInv i X))) = 1 ∧
      compositeT P.dn P.h (Ncoord (fN P PhiInv i X)) 0 ≠ 0 := by
  obtain ⟨hND, h0, -⟩ := fN_facts hΦ hi1 hik hX
  exact ⟨(Return.compositeT_nsq (dn_pos P) P.dn_lt_third _).trans hND.1,
    (Return.avoid_L (dn_pos P) P.dn_lt_third P.h_lt_dn hND h0).1⟩

/-- **`prop:rtc-embeddings` (1), smoothness.** -/
theorem contDiffAt_fcap {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {X : E4} (hX : X ∈ srcBall P i) :
    ContDiffAt ℝ ∞ (fcap P PhiInv i) X := by
  obtain ⟨hND, -, -⟩ := fN_facts hΦ hi1 hik hX
  have hN := contDiff_Ncoord.contDiffAt.comp X (Strip.Cubic.fN_smooth hΦ hi1 hik hX)
  have hT := (contDiffAt_compositeT (h := P.h) (dn_pos P) P.dn_lt_third
    (lt_of_le_of_lt hND.2.2 P.h_lt_dn)).comp X hN
  have hB := (contDiffAt_ballChart (compositeT_facts hΦ hi1 hik hX).2).comp X hT
  exact contDiff_c2ToE4.contDiffAt.comp X hB

/-- **`prop:rtc-embeddings` (3)**: `π ‖f_i^cap‖² < 1`. -/
theorem fcap_mem_ball {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {X : E4} (hX : X ∈ srcBall P i) :
    π * ‖fcap P PhiInv i X‖ ^ 2 < 1 := by
  obtain ⟨hND, h0, -⟩ := fN_facts hΦ hi1 hik hX
  rw [fcap, Return.norm_c2ToE4_sq]
  exact Return.compositeBall_mem (dn_pos P) P.dn_lt_third P.h_lt_dn hND h0

/-- **`prop:rtc-embeddings` (1), symplecticity**: `(f_i^cap)^* ω_std = ω_std`. -/
theorem fcap_symplectic {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) {X0 : E4} (hX0 : X0 ∈ srcBall P i)
    (v w : E4) :
    omega0 (fderiv ℝ (fcap P PhiInv i) X0 v) (fderiv ℝ (fcap P PhiInv i) X0 w) = omega0 v w := by
  have hdn := dn_pos P
  have hdn3 := P.dn_lt_third
  have hh := P.h_lt_dn
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (Strip.Cubic.isOpen_srcBall P i) X0 hX0
  have hψ : ∀ y, bump X0 r y ∈ srcBall P i := fun y => hball (bump_mem X0 hr y)
  have hψd : DifferentiableAt ℝ (bump X0 r) 0 := (hasFDerivAt_bump X0 hr).differentiableAt
  -- the global smooth family `φ₀ = Ncoord ∘ f_i^N ∘ bump`
  set g : E4 → E4 := fun y => fN P PhiInv i (bump X0 r y) with hg_def
  have hgs : ∀ y, ContDiffAt ℝ ∞ g y := fun y =>
    (Strip.Cubic.fN_smooth hΦ hi1 hik (hψ y)).comp y (contDiff_bump X0 hr).contDiffAt
  set φ₀ : E4 → C3 × ℂ := fun y => Ncoord (g y) with hφ₀_def
  have hφ : ContDiff ℝ ∞ φ₀ :=
    contDiff_iff_contDiffAt.mpr fun y => contDiff_Ncoord.contDiffAt.comp y (hgs y)
  have hφD : ∀ y, φ₀ y ∈ NDom P.h := fun y => (fN_facts hΦ hi1 hik (hψ y)).1
  have hT : ContDiff ℝ ∞ (fun y => compositeT P.dn P.h (φ₀ y)) :=
    contDiff_iff_contDiffAt.mpr fun y =>
      (contDiffAt_compositeT hdn hdn3 (lt_of_le_of_lt (hφD y).2.2 hh)).comp y hφ.contDiffAt
  have h1 := Return.compositeT_pullback hdn hdn3 hh hφ hφD
  have h2 := Return.ballChart_symplectic_rep' P.dn hT
    (fun y => (compositeT_facts hΦ hi1 hik (hψ y)).1)
    (fun y => (compositeT_facts hΦ hi1 hik (hψ y)).2)
  have h3 := congrArg (fun B : E4 →L[ℝ] E4 →L[ℝ] ℝ => B v w) (congrFun (h2.trans h1) 0)
  simp only [pull2_apply] at h3
  -- left side: the derivative of `f_i^cap ∘ bump` at `0` is `D f_i^cap (X₀)`
  have hfd : DifferentiableAt ℝ (fcap P PhiInv i) (bump X0 r 0) := by
    rw [bump_zero]; exact (contDiffAt_fcap hΦ hi1 hik hX0).differentiableAt (by simp)
  have eL : (fun y => c2ToE4 (ballChart (compositeT P.dn P.h (φ₀ y)))) =
      fcap P PhiInv i ∘ bump X0 r := rfl
  rw [eL, fderiv_comp 0 hfd hψd, fderiv_bump X0 hr, bump_zero] at h3
  -- right side: `ι ∘ Ncoord` pulls `Ω_E` back to `Ω₀`, and `f_i^N` pulls `Ω₀` back to `ω_std`
  obtain ⟨-, -, hp⟩ := fN_facts hΦ hi1 hik hX0
  have hId : DifferentiableAt ℝ (fun Y => injection P.dn (Ncoord Y)) (g 0) := by
    rw [Return.injection_Ncoord]
    exact (Return.contDiffAt_PhiN (by rw [hg_def]; simp only [bump_zero]; linarith)).differentiableAt
      (by simp)
  have hgd : DifferentiableAt ℝ g 0 := (hgs 0).differentiableAt (by simp)
  have eR : (fun y => injection P.dn (φ₀ y)) = (fun Y => injection P.dn (Ncoord Y)) ∘ g := rfl
  have hfNd : DifferentiableAt ℝ (fN P PhiInv i) (bump X0 r 0) := by
    rw [bump_zero]; exact (Strip.Cubic.fN_smooth hΦ hi1 hik hX0).differentiableAt (by simp)
  have eg : g = fN P PhiInv i ∘ bump X0 r := rfl
  rw [eR, fderiv_comp 0 hId hgd] at h3
  have hpb := Return.injection_pullback (dn := P.dn) (X := g 0)
    (by rw [hg_def]; simp only [bump_zero]; linarith)
  have hpb' := congrArg (fun B : E4 →L[ℝ] E4 →L[ℝ] ℝ =>
    B (fderiv ℝ g 0 v) (fderiv ℝ g 0 w)) hpb
  simp only [pull2_apply] at hpb'
  simp only [ContinuousLinearMap.comp_apply] at h3
  have hsym := Strip.Cubic.fN_symplectic hΦ hi1 hik hX0 v w
  rw [pull2_apply, OmegaT_zero_apply] at hsym
  rw [eg, fderiv_comp 0 hfNd hψd, fderiv_bump X0 hr, bump_zero] at hpb'
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    bump_zero] at hpb' h3
  simp only [Return.ωstd, Return.omegaStd_apply] at h3
  rw [hφ₀_def, eg, fderiv_comp 0 hfNd hψd, fderiv_bump X0 hr] at h3
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    bump_zero] at h3
  rw [h3, hpb', ← hsym]

/-! ### Injectivity and disjointness -/

omit hΦ in
lemma DinvN_apply3 (Y : E4) : Strip.Cubic.DinvN P Y 3 = Y 3 := by
  simp [Strip.Cubic.DinvN, Handle.chartA]

/-- **Equal values of `f^cap` come from equal values of `f^N`**: injectivity of `b_ball ∘ 𝒯`
modulo gauge, of `Ncoord` modulo deck and gauge, deck-equivariance of `Φ⁻¹` and the fact that
`𝒟⁻¹ ∘ E_i` lands in the band `(1/8, 5/24)²`. -/
theorem fcap_eq_imp (hD : DeckEquivariant PhiInv) {i j : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k)
    (hj1 : 1 ≤ j) (hjk : j ≤ P.k) {X X' : E4} (hX : X ∈ srcBall P i) (hX' : X' ∈ srcBall P j)
    (h : fcap P PhiInv i X = fcap P PhiInv j X') : fN P PhiInv i X = fN P PhiInv j X' := by
  have hdn := dn_pos P
  have hdn3 := P.dn_lt_third
  have hh := P.h_lt_dn
  obtain ⟨hND, -, -⟩ := fN_facts hΦ hi1 hik hX
  obtain ⟨hND', -, -⟩ := fN_facts hΦ hj1 hjk hX'
  obtain ⟨hu, h0⟩ := compositeT_facts hΦ hi1 hik hX
  obtain ⟨hu', h0'⟩ := compositeT_facts hΦ hj1 hjk hX'
  obtain ⟨μ, hμ, hZ⟩ := ballChart_inj hu hu' h0 h0' (c2ToE4_injective h)
  have hg := Return.compositeT_inj_mod_gauge hdn hdn3 hh hND hND' hμ hZ
  obtain ⟨T, m, n, hT, hQ⟩ := gauge_imp_deck hD hμ hg
  obtain ⟨hY2, -, hZ2, hZp⟩ := Strip.Cubic.fN_aux hΦ hi1 hik hX
  obtain ⟨hY2', -, hZ2', hZp'⟩ := Strip.Cubic.fN_aux hΦ hj1 hjk hX'
  set Y := Strip.Cubic.DinvN P (Strip.Cubic.layerMap P i X)
  set Y' := Strip.Cubic.DinvN P (Strip.Cubic.layerMap P j X')
  have hQY : fN P PhiInv i X = PhiInv Y := rfl
  have hQY' : fN P PhiInv j X' = PhiInv Y' := rfl
  have hYY : Y = T Y' := by
    have e : PhiInv Y = PhiInv (T Y') := by rw [hT.comm, ← hQY, ← hQY']; exact hQ
    have e' := congrArg Phi e
    rwa [hΦ.left_inv _ hZp, hΦ.left_inv _ (by rw [hT.pE_eq]; exact hZp')] at e'
  have hv : Y 3 ∈ Ioo (1 / 8 : ℝ) (5 / 24) := by
    rw [DinvN_apply3]; exact (Strip.Cubic.layerMap_mem P hi1 hik hX).1.1.2
  have hv' : Y' 3 ∈ Ioo (1 / 8 : ℝ) (5 / 24) := by
    rw [DinvN_apply3]; exact (Strip.Cubic.layerMap_mem P hj1 hjk hX').1.1.2
  have hE := hT.eq_of_band hYY hZ2 hZ2' hv hv'
  rw [hQY, hQY', hE]

/-- **`prop:rtc-embeddings` (1), injectivity** on `𝔹_{ρ̂}`. -/
theorem fcap_injective (hD : DeckEquivariant PhiInv) {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) :
    InjOn (fcap P PhiInv i) (srcBall P i) := fun _ hX _ hX' h =>
  Strip.Cubic.layerMap_injective P hi1 hik hX hX'
    (Strip.Cubic.fN_eq_imp hΦ hi1 hik hi1 hik hX hX' (fcap_eq_imp hΦ hD hi1 hik hi1 hik hX hX' h))

/-- **`prop:rtc-embeddings` (2), disjointness.** -/
theorem fcap_disjoint (hD : DeckEquivariant PhiInv) {i j : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k)
    (hj1 : 1 ≤ j) (hjk : j ≤ P.k) (hij : i ≠ j) :
    Disjoint (fcap P PhiInv i '' srcBall P i) (fcap P PhiInv j '' srcBall P j) := by
  rw [Set.disjoint_left]
  rintro _ ⟨X, hX, rfl⟩ ⟨X', hX', h⟩
  have := Strip.Cubic.fN_eq_imp hΦ hj1 hjk hi1 hik hX' hX (fcap_eq_imp hΦ hD hj1 hjk hi1 hik hX' hX h)
  exact Set.disjoint_left.mp (Strip.Cubic.layerMap_disjoint P hi1 hik hj1 hjk hij) ⟨X, hX, rfl⟩ ⟨X', hX', this⟩

end cap

/-! ### The concrete Moser map -/

theorem handle_phiInvSpec (P : Branch2.VCubic) :
    Strip.Cubic.PhiInvSpec P (Handle.Cubic.handlePhi P) (Handle.Cubic.handlePhiInv P) := by
  obtain ⟨hs, hpb, -, hm, hl, hf⟩ := Handle.Cubic.handle_phiInvSpec_strip P
  refine ⟨hs, fun X hX hA => hpb X hX ?_, hm, hl, hf⟩
  obtain ⟨h1, h2⟩ := hA
  simp only [Handle.stripU, Set.mem_setOf_eq, Bundle.u0, Bundle.u1]
  constructor <;> linarith

/-- **The capacity-scale embeddings of valid cubic data** with the concrete handle Moser map. -/
def fcapV (P : Branch2.VCubic) (i : ℕ) : E4 → E4 := fcap P (Handle.Cubic.handlePhiInv P) i

lemma mem_srcBall_iff (P : Branch2.VCubic) (i : ℕ) (X : E4) :
    X ∈ srcBall P i ↔ π * ‖X‖ ^ 2 < P.rhoHat i := by
  rw [Strip.norm_sq_E4]
  simp only [srcBall, mem_setOf_eq]
  constructor <;> intro h <;> linarith

variable (P : Branch2.VCubic) {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k)
include hi1 hik

theorem fcapV_smooth {X : E4} (hX : π * ‖X‖ ^ 2 < P.rhoHat i) : ContDiffAt ℝ ∞ (fcapV P i) X :=
  contDiffAt_fcap (handle_phiInvSpec P) hi1 hik ((mem_srcBall_iff P i X).mpr hX)

theorem fcapV_symplectic {X : E4} (hX : π * ‖X‖ ^ 2 < P.rhoHat i) :
    IsSymplecticLinear (fderiv ℝ (fcapV P i) X) := fun v w =>
  fcap_symplectic (handle_phiInvSpec P) hi1 hik ((mem_srcBall_iff P i X).mpr hX) v w

theorem fcapV_injective : InjOn (fcapV P i) {X | π * ‖X‖ ^ 2 < P.rhoHat i} := by
  have h := fcap_injective (handle_phiInvSpec P) (Handle.Cubic.handle_deckEquivariant P) hi1 hik
  intro X hX X' hX' e
  exact h ((mem_srcBall_iff P i X).mpr hX) ((mem_srcBall_iff P i X').mpr hX') e

theorem fcapV_mem_ball {X : E4} (hX : π * ‖X‖ ^ 2 < P.rhoHat i) : π * ‖fcapV P i X‖ ^ 2 < 1 :=
  fcap_mem_ball (handle_phiInvSpec P) hi1 hik ((mem_srcBall_iff P i X).mpr hX)

omit hi1 hik in
theorem fcapV_disjoint {i j : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ P.k) (hj1 : 1 ≤ j) (hjk : j ≤ P.k)
    (hij : i ≠ j) :
    Disjoint (fcapV P i '' {X | π * ‖X‖ ^ 2 < P.rhoHat i})
      (fcapV P j '' {X | π * ‖X‖ ^ 2 < P.rhoHat j}) := by
  have h := fcap_disjoint (handle_phiInvSpec P) (Handle.Cubic.handle_deckEquivariant P) hi1 hik
    hj1 hjk hij
  have e : ∀ l, {X : E4 | π * ‖X‖ ^ 2 < P.rhoHat l} = srcBall P l := fun l => by
    ext X; exact (mem_srcBall_iff P l X).symm
  rw [e, e]; exact h

end SymplecticPacking.Embed.Cubic
