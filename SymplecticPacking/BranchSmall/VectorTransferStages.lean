import SymplecticPacking.BranchSmall.VectorTransfer
import SymplecticPacking.BranchSmall.VectorTransferSpecFlow
import SymplecticPacking.BranchSmall.ReturnControl
import SymplecticPacking.BranchSmall.TransportTrajectory
import SymplecticPacking.BranchSmall.TransportGraph
import SymplecticPacking.BranchSmall.TransferMapForm
import SymplecticPacking.HighDim.Comparator.Isotopy
import OAI.Geometry.BallPacking.Models.RationalSlack

/-!
# Stage decomposition of `vectorTransfer_spec` (paper thm:qdr-transfer; supplement thm:vtr-transfer)

`VT.transferMap a b = affineRadialTarget ∘ ψ₁⁻¹ ∘ pr ∘ τ₁ ∘ ι_b` on the curve tube
`D₀ = {(z, U) : z ∈ locus a, π|U|² < b}`. This file proves:

* the radial injection `ι_b` is smooth near `D₀` and has an explicit continuous left inverse
  `(z, W) ↦ (z, √(b/π) W / ((1 + |z|²) √(1 + u)))` (supplement lem:vtr-injection);
* the projection `pr` has the continuous left inverse `z ↦ (z, equations a z)` on the graph `X₁`;
* the ball chart has a continuous left inverse on its range (it is an embedding);
* the abstract assembly: smoothness of the composite at every point of `D₀`, a continuous
  left inverse of the composite on `D₀`, and from these the manifold statements
  (`ContMDiffOn`, `IsEmbedding`) for the map on `Surface m × Fibre (m + 2)`.

The smoothness and inverse statements for transport and Moser return follow from
`TransportTrajectory.lean` and `ReturnControl.lean` through the interval-flow
comparison in `VectorTransferSpecFlow.lean`. `TransportGraph.lean` proves the
endpoint constraint, and `TransferMapForm.lean` proves the symplectic identity.
-/

noncomputable section

namespace SymplecticPacking.BranchSmall

open Set Manifold
open SymplecticPacking.HighDim
open OAI.PackingSufficiencySupport (Ambient openBall)
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold

/-! ### Continuous left inverses -/

/-- `f` has a left inverse on `s` that is continuous on `f '' s`. -/
def HasCtsLeftInvOn {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (f : α → β) (s : Set α) : Prop :=
  ∃ g : β → α, ContinuousOn g (f '' s) ∧ LeftInvOn g f s

section leftInv

variable {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

theorem HasCtsLeftInvOn.mono {f : α → β} {s t : Set α} (h : HasCtsLeftInvOn f t) (hst : s ⊆ t) :
    HasCtsLeftInvOn f s := by
  obtain ⟨g, hg, hgf⟩ := h
  exact ⟨g, hg.mono (image_mono hst), hgf.mono hst⟩

theorem HasCtsLeftInvOn.comp {f : α → β} {g : β → γ} {s : Set α}
    (hf : HasCtsLeftInvOn f s) (hg : HasCtsLeftInvOn g (f '' s)) :
    HasCtsLeftInvOn (g ∘ f) s := by
  obtain ⟨f', hf', hff⟩ := hf
  obtain ⟨g', hg', hgg⟩ := hg
  refine ⟨f' ∘ g', ?_, ?_⟩
  · rw [image_comp]
    refine hf'.comp hg' ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [hgg hy]
    exact hy
  · intro x hx
    simp only [Function.comp_apply]
    rw [hgg (mem_image_of_mem f hx), hff hx]

theorem hasCtsLeftInvOn_of_continuous {f : α → β} {g : β → α} {s : Set α}
    (hg : Continuous g) (hgf : LeftInvOn g f s) : HasCtsLeftInvOn f s :=
  ⟨g, hg.continuousOn, hgf⟩

theorem hasCtsLeftInvOn_of_isEmbedding [Nonempty α] {f : α → β} (hf : Topology.IsEmbedding f)
    (s : Set α) : HasCtsLeftInvOn f s := by
  classical
  let e := hf.toHomeomorph
  let g : β → α := fun y => if hy : y ∈ range f then e.symm ⟨y, hy⟩ else Classical.arbitrary α
  have hgr : ∀ y (hy : y ∈ range f), g y = e.symm ⟨y, hy⟩ := fun y hy => by
    simp only [g, dif_pos hy]
  refine ⟨g, ?_, ?_⟩
  · have hc : ContinuousOn g (range f) := by
      have hcont : Continuous (fun y : range f => g y) := by
        have : (fun y : range f => g y) = fun y => e.symm y := funext fun y => hgr y.1 y.2
        rw [this]
        exact e.symm.continuous
      exact continuousOn_iff_continuous_restrict.2 hcont
    exact hc.mono (image_subset_range f s)
  · intro x _
    rw [hgr (f x) (mem_range_self x)]
    exact hf.toHomeomorph_symm_apply x

/-- A map with a continuous left inverse on the range of an embedding is an embedding after
composition with it. -/
theorem isEmbedding_comp_of_leftInv {i : α → β} (hi : Topology.IsEmbedding i) {G : β → γ}
    (hG : ContinuousOn G (range i)) (hinv : HasCtsLeftInvOn G (range i)) :
    Topology.IsEmbedding (G ∘ i) := by
  obtain ⟨g, hg, hgG⟩ := hinv
  let S := G '' range i
  let f' : α → S := fun x => ⟨G (i x), i x, mem_range_self x, rfl⟩
  have hf' : Continuous f' := by
    apply Continuous.subtype_mk
    exact hG.comp_continuous hi.continuous mem_range_self
  have hg' : Continuous (S.restrict g) := hg.restrict
  have hcomp : S.restrict g ∘ f' = i := by
    funext x
    exact hgG (mem_range_self x)
  have hind : Topology.IsInducing f' :=
    Topology.IsInducing.of_comp hf' hg' (hcomp ▸ hi.isInducing)
  refine ⟨(Topology.IsInducing.subtypeVal).comp hind, ?_⟩
  intro x y hxy
  apply hi.injective
  have hx := hgG (mem_range_self x)
  have hy := hgG (mem_range_self y)
  simp only [Function.comp_apply] at hxy
  rw [← hx, ← hy, hxy]

end leftInv

/-! ### The curve tube and the stages -/

namespace VT

variable {q : ℕ}

/-- The inverse of `toC`. -/
def fromC (w : Fin q → ℂ) : PlanePhase (Fin q) := fun j => ((w j).re, (w j).im)

@[simp] theorem fromC_toC (x : PlanePhase (Fin q)) : fromC (toC x) = x := by
  funext j
  rfl

theorem toC_continuous : Continuous (toC (q := q)) := by
  apply continuous_pi
  intro j
  exact (Complex.equivRealProdCLM.symm.continuous).comp (continuous_apply j)

theorem toC_contDiff : ContDiff ℝ ∞ (toC (q := q)) := by
  apply contDiff_pi.2
  intro j
  exact (Complex.equivRealProdCLM.symm.contDiff).comp (contDiff_apply ℝ (ℝ × ℝ) j)

theorem fromC_continuous : Continuous (fromC (q := q)) := by
  apply continuous_pi
  intro j
  exact (Complex.continuous_re.comp (continuous_apply j)).prodMk
    (Complex.continuous_im.comp (continuous_apply j))

/-- The curve tube `D₀ = {(z, U) : z ∈ locus a, π|U|² < b}`. -/
def tube (a : Fin q → ℂ) (b : ℝ) : Set (Affine q × PlanePhase (Fin q)) :=
  {x | x.1 ∈ locus a ∧ Real.pi * wsq (toC x.2) < b}

/-- Stage one: `x ↦ ι_b(x)`. -/
def stageR (b : ℝ) (x : Affine q × PlanePhase (Fin q)) : Tot q := radialInj b x.1 (toC x.2)

/-- The radial factor of `ι_b`. -/
def radialFactor (b : ℝ) (z : Affine q) (w : Fin q → ℂ) : ℝ :=
  (1 + nsq z) * Real.sqrt Real.pi / Real.sqrt (b - Real.pi * wsq w)

/-- The radial factor of `ι_b⁻¹`: `√(b/π) / ((1 + |z|²) √(1 + u))`. -/
def inverseFactor (b : ℝ) (y : Tot q) : ℝ :=
  Real.sqrt (b / Real.pi) / ((1 + nsq y.1) * Real.sqrt (1 + wsq y.2 / (1 + nsq y.1) ^ 2))

/-- The explicit inverse of `ι_b`. -/
def stageRInv (b : ℝ) (y : Tot q) : Affine q × PlanePhase (Fin q) :=
  (y.1, fromC fun j => ((inverseFactor b y : ℝ) : ℂ) * y.2 j)

theorem wsq_continuous : Continuous (wsq (q := q)) :=
  continuous_finset_sum _ fun j _ => Complex.continuous_normSq.comp (continuous_apply j)

theorem nsq_continuous : Continuous (nsq (q := q)) :=
  (Complex.continuous_normSq.comp continuous_fst).add (wsq_continuous.comp continuous_snd)

theorem inverseFactor_continuous (b : ℝ) : Continuous (inverseFactor (q := q) b) := by
  unfold inverseFactor
  apply Continuous.div continuous_const
  · apply Continuous.mul
    · exact continuous_const.add (nsq_continuous.comp continuous_fst)
    · apply Real.continuous_sqrt.comp
      apply continuous_const.add
      apply Continuous.div (wsq_continuous.comp continuous_snd)
      · exact (continuous_const.add (nsq_continuous.comp continuous_fst)).pow 2
      · intro y; exact (pow_pos (one_add_nsq_pos y.1) 2).ne'
  · intro y
    apply mul_ne_zero (one_add_nsq_pos y.1).ne'
    have := wsq_nonneg y.2
    have := one_add_nsq_pos y.1
    exact (Real.sqrt_pos.2 (by positivity)).ne'

theorem stageRInv_continuous (b : ℝ) : Continuous (stageRInv (q := q) b) := by
  unfold stageRInv
  apply continuous_fst.prodMk
  apply fromC_continuous.comp
  apply continuous_pi
  intro j
  exact (Complex.continuous_ofReal.comp (inverseFactor_continuous b)).mul
    ((continuous_apply j).comp continuous_snd)

theorem inverseFactor_mul_radialFactor {b : ℝ} (z : Affine q) (w : Fin q → ℂ)
    (hw : Real.pi * wsq w < b) :
    inverseFactor b (radialInj b z w) * radialFactor b z w = 1 := by
  have hz := one_add_nsq_pos z
  have hd : 0 < b - Real.pi * wsq w := by linarith
  have hπ := Real.pi_pos
  have hb : 0 < b := by have := wsq_nonneg w; nlinarith
  have hu := radialInj_u z w hw
  unfold inverseFactor radialFactor
  simp only [radialInj_fst]
  rw [hu]
  have h1 : 0 < 1 + Real.pi * wsq w / (b - Real.pi * wsq w) := by
    have := wsq_nonneg w; positivity
  set P := Real.pi * wsq w
  have hpos : 0 ≤ Real.sqrt (b / Real.pi) / ((1 + nsq z) * Real.sqrt (1 + P / (b - P))) *
      ((1 + nsq z) * Real.sqrt Real.pi / Real.sqrt (b - P)) := by positivity
  have hsq : (Real.sqrt (b / Real.pi) / ((1 + nsq z) * Real.sqrt (1 + P / (b - P))) *
      ((1 + nsq z) * Real.sqrt Real.pi / Real.sqrt (b - P))) ^ 2 = 1 := by
    rw [mul_pow, div_pow, div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity),
      Real.sq_sqrt h1.le, Real.sq_sqrt hπ.le, Real.sq_sqrt hd.le]
    field_simp
    ring_nf
    exact mul_inv_cancel₀ hb.ne'
  nlinarith [hpos, hsq]

theorem stageRInv_stageR {b : ℝ} (x : Affine q × PlanePhase (Fin q))
    (hx : Real.pi * wsq (toC x.2) < b) : stageRInv b (stageR b x) = x := by
  have h := inverseFactor_mul_radialFactor x.1 (toC x.2) hx
  unfold stageRInv stageR
  rw [radialInj_fst]
  ext1
  · rfl
  · change fromC (fun j => ((inverseFactor b (radialInj b x.1 (toC x.2)) : ℝ) : ℂ) *
      (((radialFactor b x.1 (toC x.2) : ℝ) : ℂ) * toC x.2 j)) = x.2
    have : (fun j => ((inverseFactor b (radialInj b x.1 (toC x.2)) : ℝ) : ℂ) *
        (((radialFactor b x.1 (toC x.2) : ℝ) : ℂ) * toC x.2 j)) = toC x.2 := by
      funext j
      rw [← mul_assoc, ← Complex.ofReal_mul, h, Complex.ofReal_one, one_mul]
    rw [this, fromC_toC]

theorem stageR_hasCtsLeftInvOn (a : Fin q → ℂ) (b : ℝ) :
    HasCtsLeftInvOn (stageR (q := q) b) (tube a b) :=
  hasCtsLeftInvOn_of_continuous (stageRInv_continuous b) fun x hx => stageRInv_stageR x hx.2

theorem wsq_contDiff : ContDiff ℝ ∞ (wsq (q := q)) := by
  unfold wsq
  apply ContDiff.sum
  intro j _
  have : (fun w : Fin q → ℂ => Complex.normSq (w j)) =
      fun w => (w j).re * (w j).re + (w j).im * (w j).im := by
    funext w; exact Complex.normSq_apply _
  rw [this]
  have hre : ContDiff ℝ ∞ (fun w : Fin q → ℂ => (w j).re) :=
    Complex.reCLM.contDiff.comp (contDiff_apply ℝ ℂ j)
  have him : ContDiff ℝ ∞ (fun w : Fin q → ℂ => (w j).im) :=
    Complex.imCLM.contDiff.comp (contDiff_apply ℝ ℂ j)
  exact (hre.mul hre).add (him.mul him)

theorem nsq_contDiff : ContDiff ℝ ∞ (nsq (q := q)) := by
  unfold nsq
  have h1 : ContDiff ℝ ∞ (fun z : Affine q => Complex.normSq z.1) := by
    have : (fun z : Affine q => Complex.normSq z.1) =
        fun z => z.1.re * z.1.re + z.1.im * z.1.im := by
      funext z; exact Complex.normSq_apply _
    rw [this]
    have hre : ContDiff ℝ ∞ (fun z : Affine q => z.1.re) := Complex.reCLM.contDiff.comp contDiff_fst
    have him : ContDiff ℝ ∞ (fun z : Affine q => z.1.im) := Complex.imCLM.contDiff.comp contDiff_fst
    exact (hre.mul hre).add (him.mul him)
  exact h1.add (wsq_contDiff.comp contDiff_snd)

/-- `ι_b` is smooth near every point of the open tube `{π|U|² < b}`. -/
theorem stageR_contDiffAt {b : ℝ} (x : Affine q × PlanePhase (Fin q))
    (hx : Real.pi * wsq (toC x.2) < b) : ContDiffAt ℝ ∞ (stageR (q := q) b) x := by
  have hP : ContDiff ℝ ∞ (fun x : Affine q × PlanePhase (Fin q) => Real.pi * wsq (toC x.2)) :=
    contDiff_const.mul (wsq_contDiff.comp (toC_contDiff.comp contDiff_snd))
  have hr : ContDiffAt ℝ ∞
      (fun x : Affine q × PlanePhase (Fin q) => radialFactor b x.1 (toC x.2)) x := by
    unfold radialFactor
    apply ContDiffAt.div
    · exact ((contDiff_const.add (nsq_contDiff.comp contDiff_fst)).mul contDiff_const).contDiffAt
    · apply ContDiffAt.sqrt (contDiff_const.sub hP).contDiffAt
      exact (by linarith : (0:ℝ) < b - Real.pi * wsq (toC x.2)).ne'
    · exact (Real.sqrt_pos.2 (by linarith)).ne'
  unfold stageR radialInj
  apply contDiffAt_fst.prodMk
  apply contDiffAt_pi.2
  intro j
  have hc : ContDiffAt ℝ ∞ (fun x : Affine q × PlanePhase (Fin q) =>
      ((radialFactor b x.1 (toC x.2) : ℝ) : ℂ)) x :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp x hr
  exact hc.mul ((contDiff_apply ℝ ℂ j).comp (toC_contDiff.comp contDiff_snd)).contDiffAt

/-! ### The analytic stage inputs (transport and Moser return) -/

/-- **Transport, local control** (prop:vtr-transport (c)–(e)): for
every `x` in the curve tube the transport field `transportField` (the `Ω_b`-orthogonal lift,
smooth where its linear problem is uniquely solvable) agrees, on an open set containing the
trajectory of `ι_b(x)` over `T ∈ [0,1]`, with a compactly supported smooth field (a cutoff).
The generic consequences (unique `[0,1]`-solution, smoothness, backward inverse) are proved in
`VectorTransferSpecFlow.lean`. -/
theorem transport_control (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (x : Affine (m + 2) × PlanePhase (Fin (m + 2))) (hx : x ∈ tube (parameters m) b) :
    LocalControl (transportField (parameters m) b) (stageR b x) :=
  transport_control_of_inputs m hb0 hb x hx.1 hx.2

/-- **Return, local control** (prop:vtr-return (c) with prop:vtr-transport): the reversed Moser
field `s, z ↦ −Y_{1−s}(z)` is locally controlled along the trajectory from `pr τ₁ ι_b(x)`. -/
theorem return_control (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (x : Affine (m + 2) × PlanePhase (Fin (m + 2))) (hx : x ∈ tube (parameters m) b) :
    LocalControl (revField (returnField (parameters m) b))
      (transport (parameters m) b (stageR b x)).1 :=
  return_control_all m hb0 hb _

/-- **Transport, smoothness** (prop:vtr-transport (c),(e)): the time-one horizontal transport is
smooth near `ι_b(x)` for every `x` in the curve tube. -/
theorem transport_contDiffAt (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (x : Affine (m + 2) × PlanePhase (Fin (m + 2))) (hx : x ∈ tube (parameters m) b) :
    ContDiffAt ℝ ∞ (transport (parameters m) b) (stageR b x) :=
  flowI_one_contDiffAt_of_control (transport_control m hb0 hb x hx)

/-- **Transport, target** (prop:vtr-transport (a),(e)): `τ₁ ι_b(x) ∈ X₁ = {W = equations z}`. -/
theorem transport_graph (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (x : Affine (m + 2) × PlanePhase (Fin (m + 2))) (hx : x ∈ tube (parameters m) b) :
    (transport (parameters m) b (stageR b x)).2 =
      equations (parameters m) (transport (parameters m) b (stageR b x)).1 := by
  obtain ⟨γ, hγ0, hγO, hγ⟩ := transport_trajectory m hb0 hb x hx.1 hx.2
  obtain ⟨W, O, hW, hO, hVW, hy⟩ := transport_control m hb0 hb x hx
  have hu := existsUnique_isSolI hW hO hVW hy
  have hsol : IsSolI (transportField (parameters m) b) 0 (stageR b x)
      (fun s => γ (clampI s)) := by
    refine ⟨?_, fun s => ?_, fun s hs => ?_⟩
    · change γ (clampI 0) = radialInj b x.1 (toC x.2)
      rw [clampI_of_mem ⟨le_rfl, zero_le_one⟩, hγ0]
    · change γ (clampI s) = γ (clampI (clampI s))
      rw [clampI_clampI]
    · beta_reduce
      rw [clampI_of_mem hs]
      exact (hγ s hs).congr_of_mem (fun t ht => by simp only [clampI_of_mem ht]) hs
  have hT : transport (parameters m) b (stageR b x) = γ 1 := by
    unfold transport
    rw [flowI_eq hu hsol]
    simp only [clampI_of_mem (⟨zero_le_one, le_rfl⟩ : (1 : ℝ) ∈ Icc (0 : ℝ) 1)]
  rw [hT]
  refine graph_of_trajectory (parameters m) hb0 hb ?_ hγO hγ
  rw [hγ0, radialInj_fst]
  exact hx.1

/-- **Transport, inverse** (prop:vtr-transport (e)): the backward flow is a continuous inverse. -/
theorem transport_leftInv (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    HasCtsLeftInvOn (transport (parameters m) b) (stageR b '' tube (parameters m) b) :=
  flowI_one_ctsLeftInv (by
    rintro _ ⟨x, hx, rfl⟩
    exact transport_control m hb0 hb x hx)

/-- **Return, smoothness** (prop:vtr-return (c) with prop:vtr-transport): `ψ₁⁻¹` is smooth near
`pr τ₁ ι_b(x)`. -/
theorem returnInv_contDiffAt (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (x : Affine (m + 2) × PlanePhase (Fin (m + 2))) (hx : x ∈ tube (parameters m) b) :
    ContDiffAt ℝ ∞ (returnInv (parameters m) b)
      (transport (parameters m) b (stageR b x)).1 :=
  flowI_back_contDiffAt_of_control (return_control m hb0 hb x hx)

/-- **Return, inverse** (prop:vtr-return (c)): the forward Moser flow `ψ₁` is a continuous
inverse of `ψ₁⁻¹` on the projected transport image. -/
theorem returnInv_leftInv (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    HasCtsLeftInvOn (returnInv (parameters m) b)
      (Prod.fst '' (transport (parameters m) b '' (stageR b '' tube (parameters m) b))) :=
  flowI_back_ctsLeftInv (by
    rintro _ ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    exact return_control m hb0 hb x hx)

/-! ### Assembly in the affine chart -/

theorem transferMap_eq_comp (a : Fin q → ℂ) (b : ℝ) :
    transferMap a b = affineRadialTarget q (1 / Real.pi) ∘ returnInv a b ∘ Prod.fst ∘
      transport a b ∘ stageR b := rfl

theorem transferMap_contDiffAt (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (x : Affine (m + 2) × PlanePhase (Fin (m + 2))) (hx : x ∈ tube (parameters m) b) :
    ContDiffAt ℝ ∞ (transferMap (parameters m) b) x := by
  rw [transferMap_eq_comp]
  have h1 := stageR_contDiffAt (b := b) x hx.2
  have h2 := transport_contDiffAt m hb0 hb x hx
  have h3 := returnInv_contDiffAt m hb0 hb x hx
  have h4 := (affineRadialTarget_smooth (m + 2) (1 / Real.pi)).contDiffAt
    (x := returnInv (parameters m) b (transport (parameters m) b (stageR b x)).1)
  exact h4.comp x (h3.comp x (contDiffAt_fst.comp x (h2.comp x h1)))

theorem transferMap_hasCtsLeftInvOn (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    HasCtsLeftInvOn (transferMap (parameters m) b) (tube (parameters m) b) := by
  rw [transferMap_eq_comp]
  have hR := stageR_hasCtsLeftInvOn (parameters m) b
  have hT := transport_leftInv m hb0 hb
  -- the projection on the graph `X₁`
  have hP : HasCtsLeftInvOn (Prod.fst : Tot (m + 2) → Affine (m + 2))
      (transport (parameters m) b '' (stageR b '' tube (parameters m) b)) := by
    refine hasCtsLeftInvOn_of_continuous (g := fun z => (z, equations (parameters m) z))
      (continuous_id.prodMk ((equations_contDiff (parameters m)).continuous)) ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact Prod.ext rfl (transport_graph m hb0 hb x hx).symm
  have hM := returnInv_leftInv m hb0 hb
  have hA := hasCtsLeftInvOn_of_isEmbedding
    (affineRadialTarget_isEmbedding (m + 2) (one_div_pos.2 Real.pi_pos))
    (returnInv (parameters m) b '' (Prod.fst ''
      (transport (parameters m) b '' (stageR b '' tube (parameters m) b))))
  have h12 := hR.comp hT
  have h123 : HasCtsLeftInvOn (Prod.fst ∘ transport (parameters m) b ∘ stageR b)
      (tube (parameters m) b) := by
    refine h12.comp ?_
    rwa [image_comp]
  have h1234 : HasCtsLeftInvOn (returnInv (parameters m) b ∘ Prod.fst ∘
      transport (parameters m) b ∘ stageR b) (tube (parameters m) b) := by
    refine h123.comp ?_
    rwa [image_comp, image_comp]
  refine h1234.comp ?_
  rwa [image_comp, image_comp, image_comp]

end VT

/-! ### Transfer to `Surface m × Fibre (m + 2)` -/

/-- The inclusion `Surface m × Fibre (m+2) → Affine (m+2) × Fibre (m+2)`. -/
def surfaceIncl (m : ℕ) (x : Surface m × Fibre (m + 2)) : Affine (m + 2) × Fibre (m + 2) :=
  (x.1.val, x.2)

theorem surfaceIncl_contMDiff (m : ℕ) :
    ContMDiff 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, Affine (m + 2) × Fibre (m + 2)) ∞
      (surfaceIncl m) := by
  have h := (real_inclusion_contMDiff (parameters m)).prodMap
    (contMDiff_id (I := 𝓘(ℝ, Fibre (m + 2))) (M := Fibre (m + 2)) (n := ∞))
  rw [modelWithCornersSelf_prod (E := ℝ × ℝ) (F := Fibre (m + 2)),
    modelWithCornersSelf_prod (E := Affine (m + 2)) (F := Fibre (m + 2)),
    ← chartedSpaceSelf_prod]
  exact h

theorem surfaceIncl_isEmbedding (m : ℕ) : Topology.IsEmbedding (surfaceIncl m) :=
  Topology.IsEmbedding.subtypeVal.prodMap Topology.IsEmbedding.id

theorem totalMoment_eq_pi_wsq {q : ℕ} (U : Fibre q) :
    (∑ j, planeMoments U j) = Real.pi * VT.wsq (VT.toC U) := by
  rw [VT.pi_wsq_toC]
  rfl

theorem surfaceIncl_mem_tube (m : ℕ) {b : ℝ} {x : Surface m × Fibre (m + 2)}
    (hx : ∑ j, planeMoments x.2 j < b) : surfaceIncl m x ∈ VT.tube (parameters m) b :=
  ⟨x.1.property, by rw [← totalMoment_eq_pi_wsq]; exact hx⟩

/-- Smoothness on the tube (thm:qdr-transfer, first clause). -/
theorem transferMap_surface_contMDiffOn (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    ContMDiffOn 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, Ambient (m + 3)) ∞
      (fun x : Surface m × Fibre (m + 2) => VT.transferMap (parameters m) b (x.1.val, x.2))
      {x | ∑ j, planeMoments x.2 j < b} := by
  intro x hx
  have hG := VT.transferMap_contDiffAt m hb0 hb _ (surfaceIncl_mem_tube m hx)
  exact (hG.contMDiffAt.comp x (surfaceIncl_contMDiff m x)).contMDiffWithinAt

/-- Embedding on the tube (thm:qdr-transfer, second clause). -/
theorem transferMap_surface_isEmbedding (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2) :
    Topology.IsEmbedding (fun x : {x : Surface m × Fibre (m + 2) | ∑ j, planeMoments x.2 j < b} =>
      VT.transferMap (parameters m) b (x.val.1.val, x.val.2)) := by
  let i := fun x : {x : Surface m × Fibre (m + 2) | ∑ j, planeMoments x.2 j < b} =>
    surfaceIncl m x.val
  have hi : Topology.IsEmbedding i :=
    (surfaceIncl_isEmbedding m).comp Topology.IsEmbedding.subtypeVal
  have hr : range i ⊆ VT.tube (parameters m) b := by
    rintro _ ⟨x, rfl⟩
    exact surfaceIncl_mem_tube m x.property
  have hG : ContinuousOn (VT.transferMap (parameters m) b) (range i) := fun y hy =>
    (VT.transferMap_contDiffAt m hb0 hb y (hr hy)).continuousAt.continuousWithinAt
  exact isEmbedding_comp_of_leftInv hi hG ((VT.transferMap_hasCtsLeftInvOn m hb0 hb).mono hr)

/-- **Symplectic identity** (thm:vtr-transfer (a),(c): `𝒯^*ω_FS = Ω_N` and the ball chart is a
symplectomorphism `(ℂP^n ∖ L, ω_FS) → (B°(1), ω₀)`). -/
theorem transferMap_form (m : ℕ) {b : ℝ} (hb0 : 0 < b) (hb : b < 1 / 2)
    (x : Surface m × Fibre (m + 2)) (hx : ∑ j, planeMoments x.2 j < b)
    (v w : (ℝ × ℝ) × Fibre (m + 2)) :
    successorStandardForm (m + 2)
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, Ambient (m + 3))
          (fun x : Surface m × Fibre (m + 2) => VT.transferMap (parameters m) b (x.1.val, x.2)) x v)
        (mfderiv 𝓘(ℝ, (ℝ × ℝ) × Fibre (m + 2)) 𝓘(ℝ, Ambient (m + 3))
          (fun x : Surface m × Fibre (m + 2) => VT.transferMap (parameters m) b (x.1.val, x.2)) x w)
      = globalHorizontalCoupling phaseArea
          (normalHorizontalPrimitive (parameters m) 2 ∘ planeMoments) x v w := by
  have ht := surfaceIncl_mem_tube m hx
  exact transferMap_form_of m hb0 hb x hx
    (((VT.stageR_contDiffAt (b := b) _ ht.2).contMDiffAt.comp x
      (surfaceIncl_contMDiff m x)).mdifferentiableAt (by simp))
    ((VT.transport_contDiffAt m hb0 hb _ ht).differentiableAt (by simp))
    ((VT.returnInv_contDiffAt m hb0 hb _ ht).differentiableAt (by simp))
    (VT.transport_graph m hb0 hb _ ht) v w

end SymplecticPacking.BranchSmall
