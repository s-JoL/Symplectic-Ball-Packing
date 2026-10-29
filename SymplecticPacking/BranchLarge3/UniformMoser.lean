import SymplecticPacking.BranchLarge3.OAIOpen
import SymplecticPacking.Explicit
import SymplecticPacking.BranchLarge3.ExactSafetyRegularity

/-!
# Explicit uniform relative Moser transfer on a finite-dimensional vector space

Explicit version of the OpenAI theorem
`Hamiltonian.exists_uniform_compact_exact_fibre_embedding_central_into` for `M = N = E` a
finite-dimensional real vector space with a fixed basis `b`. Data: finitely many native smooth
guards certifying the source and target regions, and a smooth family of primitives
`Γ t` on `E`, nondegenerate at `t = 0` on a compact `K`, and a smooth family of maps `A (t, ·)`
(embeddings of `U ⊇ K` for `t ∈ (0, δ]`) with `d(Γ t) = A(t,·)^* Ω t` on `U` and `A(0, K) ⊆ T`.
Output: an explicit threshold `τ ∈ (0, δ]` and, for every `t ∈ (0, τ]`, the explicit map
`map t = A(t, ·) ∘ Φ_t` with `(map t)^* Ω t = d(Γ 0)` near `K`.

Construction.
* `ndeg p = (det [dΓ_t(x)(b i, b j)])²` measures nondegeneracy; `lev = min_K ndeg(0, ·)`,
  `rad = max_K Σ (b-coordinates)²`.
* `cut` is the product of three `smoothTransition` factors: equal to `1` where
  `ndeg > (3/4) lev`, `Σ coords² < rad + 1/2`, `t² < 1`, and `0` where `ndeg ≤ lev / 2`,
  `Σ coords² ≥ rad + 1`, `t² ≥ 2`.
* `field = cut • X`, where `X` is the Moser field: the unique `v` with
  `dΓ_t(x) v = -∂_t Γ_t(x)` (definite description where it is unique, `0` elsewhere).
* `flow (t, x)` is the value at `t` of the unique curve starting at `x` that solves
  `γ' = field(t, γ)` on `(-2, 2)` and equals `x` outside (definite description).
* `time` uses the initial minimum of finitely many explicit smooth guard functions and the
  maximum of their time derivatives along the complete cutoff flow on `[-1,1] × K`: if `c` is
  the initial clearance and `v = 1 + max |∂ₜ guard|`, then
  `time = min (min (δ/2) (1/4)) (c/(4v))`.

All choice in the definitions is through `Explicit.the` (unique objects), `sInf`/`sSup` of
explicitly defined sets of reals, and decidability instances.
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3.UMoser

open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Definitions -/

/-- The two-form `dΓ_t` at `x`, `p = (t, x)`. -/
def form (Γ : ℝ → ManifoldOneForm E E) (p : ℝ × E) : E →L[ℝ] E →L[ℝ] ℝ :=
  manifoldExteriorOneForm (Γ p.1) p.2

/-- The time derivative `∂_t Γ_t` at `x`, `p = (t, x)`. -/
def tprim (Γ : ℝ → ManifoldOneForm E E) (p : ℝ × E) : E →L[ℝ] ℝ :=
  manifoldTimePrimitive Γ p.1 p.2

/-- Gram determinant of a bilinear form in the basis `b`. -/
def gram (b : Basis ι ℝ E) (β : E →L[ℝ] E →L[ℝ] ℝ) : ℝ :=
  (Matrix.of fun i j => β (b i) (b j)).det

/-- Nondegeneracy measure `gram²`. -/
def ndeg (b : Basis ι ℝ E) (Γ : ℝ → ManifoldOneForm E E) (p : ℝ × E) : ℝ :=
  gram b (form Γ p) ^ 2

/-- Squared coordinate norm. -/
def qn (b : Basis ι ℝ E) (x : E) : ℝ := ∑ i, (b.repr x i) ^ 2

/-- `lev = inf_K ndeg (0, ·)`. -/
def lev (b : Basis ι ℝ E) (Γ : ℝ → ManifoldOneForm E E) (K : Set E) : ℝ :=
  sInf ((fun x => ndeg b Γ (0, x)) '' K)

/-- `rad = sup_K qn`. -/
def rad (b : Basis ι ℝ E) (K : Set E) : ℝ := sSup (qn b '' K)

/-- The explicit cutoff. -/
def cut (b : Basis ι ℝ E) (Γ : ℝ → ManifoldOneForm E E) (K : Set E) (p : ℝ × E) : ℝ :=
  Real.smoothTransition (4 * ndeg b Γ p / lev b Γ K - 2) *
    Real.smoothTransition (2 * (rad b K + 1 - qn b p.2)) *
    Real.smoothTransition (2 - p.1 ^ 2)

/-- The Moser field: the unique `v` with `dΓ_t(x) v = -∂_tΓ_t(x)` (where unique). -/
def mfield (Γ : ℝ → ManifoldOneForm E E) (p : ℝ × E) : E :=
  open Classical in
  if h : ∃! v : E, form Γ p v = -tprim Γ p then Explicit.the h else 0

/-- The cut-off Moser field. -/
def field (b : Basis ι ℝ E) (Γ : ℝ → ManifoldOneForm E E) (K : Set E) (p : ℝ × E) : E :=
  cut b Γ K p • mfield Γ p

/-- The curve property defining the flow line from `x`. -/
def CurveP (b : Basis ι ℝ E) (Γ : ℝ → ManifoldOneForm E E) (K : Set E) (x : E)
    (γ : ℝ → E) : Prop :=
  γ 0 = x ∧ (∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt γ (field b Γ K (t, γ t)) t) ∧
    ∀ t ∉ Ioo (-2 : ℝ) 2, γ t = x

/-- The flow line from `x` (the unique curve with `CurveP`). -/
def curve (b : Basis ι ℝ E) (Γ : ℝ → ManifoldOneForm E E) (K : Set E) (x : E) : ℝ → E :=
  open Classical in
  if h : ∃! γ, CurveP b Γ K x γ then Explicit.the h else fun _ => x

/-- The explicit Moser flow. -/
def flow (b : Basis ι ℝ E) (Γ : ℝ → ManifoldOneForm E E) (K : Set E) (p : ℝ × E) : E :=
  curve b Γ K p.2 p.1

/-- The region where `cut = 1`, the flow stays in `U` and `A` maps into `T`. -/
def region (b : Basis ι ℝ E) (Γ : ℝ → ManifoldOneForm E E) (K U : Set E) (A : ℝ × E → E)
    (T : Set E) : Set (ℝ × E) :=
  {p | 1 < 4 * ndeg b Γ p / lev b Γ K - 2 ∧ 1 < 2 * (rad b K + 1 - qn b p.2) ∧
    1 < 2 - p.1 ^ 2 ∧ p.2 ∈ U ∧ A p ∈ T}

/-- Three cutoff margins followed by the supplied finite geometric guards. -/
def guards {n : ℕ} (b : Basis ι ℝ E) (Γ : ℝ → ManifoldOneForm E E) (K : Set E)
    (g : Fin n → ℝ × E → ℝ) (i : Fin (3+n)) (p : ℝ × E) : ℝ :=
  Fin.addCases (fun j : Fin 3 =>
    ![4*ndeg b Γ p/lev b Γ K-3, 2*(rad b K+1-qn b p.2)-1, 1-p.1^2] j)
    (fun j => g j p) i

/-- Compact initial clearance divided by a compact time-derivative bound along the 
complete cutoff flow. The geometric guards are finite input formulas, not an open-set oracle. -/
def time {n : ℕ} (b : Basis ι ℝ E) (Γ : ℝ → ManifoldOneForm E E) (K : Set E)
    (δ : ℝ) (g : Fin n → ℝ × E → ℝ) : ℝ :=
  ExactSafety.time (fun i p => guards b Γ K g i (p.1, flow b Γ K p)) K δ

/-- The explicit transfer map at parameter `t`. -/
def map (b : Basis ι ℝ E) (Γ : ℝ → ManifoldOneForm E E) (K : Set E) (A : ℝ × E → E)
    (t : ℝ) (x : E) : E :=
  A (t, flow b Γ K (t, x))

/-! ### Smoothness of the data -/

theorem form_contDiff {Γ : ℝ → ManifoldOneForm E E} (hΓ : SmoothOneFormFamily Γ) :
    ContDiff ℝ ∞ (form Γ) := by
  have h := manifoldExteriorOneForm_path_smooth hΓ (0 : E)
  simp only [vector_chartTwoForm, extChartAt_model_space_eq_id, PartialEquiv.refl_target,
    univ_prod_univ, contDiffOn_univ] at h
  exact h

theorem tprim_contDiff {Γ : ℝ → ManifoldOneForm E E} (hΓ : SmoothOneFormFamily Γ) :
    ContDiff ℝ ∞ (tprim Γ) := by
  have h := manifoldTimePrimitive_smooth hΓ (0 : E)
  simp only [vector_chartOneForm, extChartAt_model_space_eq_id, PartialEquiv.refl_target,
    univ_prod_univ, contDiffOn_univ] at h
  exact h

theorem gram_contDiff (b : Basis ι ℝ E) {f : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (fun p => gram b (f p)) := by
  unfold gram
  simp only [Matrix.det_apply, Matrix.of_apply, Units.smul_def, zsmul_eq_mul]
  refine ContDiff.sum fun σ _ => ?_
  exact contDiff_const.mul
    (contDiff_prod fun i _ => (hf.clm_apply contDiff_const).clm_apply contDiff_const)

theorem ndeg_contDiff (b : Basis ι ℝ E) {Γ : ℝ → ManifoldOneForm E E}
    (hΓ : SmoothOneFormFamily Γ) : ContDiff ℝ ∞ (ndeg b Γ) :=
  (gram_contDiff b (form_contDiff hΓ)).pow 2

theorem qn_eq (b : Basis ι ℝ E) (x : E) : qn b x = ∑ i, (b.equivFunL x i) ^ 2 := by
  simp [qn]

theorem qn_contDiff (b : Basis ι ℝ E) : ContDiff ℝ ∞ (qn b) := by
  have h : qn b = fun x => ∑ i, (b.equivFunL x i) ^ 2 := funext (qn_eq b)
  rw [h]
  refine ContDiff.sum fun i _ => ?_
  exact (((ContinuousLinearMap.proj i).comp
    b.equivFunL.toContinuousLinearMap).contDiff).pow 2

theorem isCompact_qn_le (b : Basis ι ℝ E) (M : ℝ) : IsCompact {x | qn b x ≤ M} := by
  have hs : {x | qn b x ≤ M} = b.equivFunL ⁻¹' {c : ι → ℝ | ∑ i, c i ^ 2 ≤ M} := by
    ext x
    simp only [mem_setOf_eq, mem_preimage, qn_eq]
  rw [hs]
  apply b.equivFunL.toHomeomorph.isCompact_preimage.mpr
  apply Metric.isCompact_of_isClosed_isBounded
  · exact isClosed_le (continuous_finset_sum _ fun i _ => (continuous_apply i).pow 2)
      continuous_const
  · rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨Real.sqrt M, fun c hc => ?_⟩
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg M)).mpr fun i => ?_
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    calc c i ^ 2 ≤ ∑ j, c j ^ 2 :=
          Finset.single_le_sum (f := fun j => c j ^ 2) (fun j _ => sq_nonneg _)
            (Finset.mem_univ i)
      _ ≤ M := hc

/-! ### Nondegeneracy and the Gram determinant -/

theorem gram_apply_sum (b : Basis ι ℝ E) (β : E →L[ℝ] E →L[ℝ] ℝ) (c : ι → ℝ) (j : ι) :
    β (∑ i, c i • b i) (b j) = (Matrix.vecMul c (Matrix.of fun i j => β (b i) (b j))) j := by
  simp [Matrix.vecMul, dotProduct, map_sum, map_smul, ContinuousLinearMap.sum_apply]

theorem clm_eq_zero_of_basis (b : Basis ι ℝ E) {f : E →L[ℝ] ℝ} (h : ∀ j, f (b j) = 0) :
    f = 0 := by
  apply ContinuousLinearMap.coe_injective
  exact b.ext fun j => by simpa using h j

theorem gram_ne_zero_of_isInvertible (b : Basis ι ℝ E) {β : E →L[ℝ] E →L[ℝ] ℝ}
    (h : β.IsInvertible) : gram b β ≠ 0 := by
  intro h0
  obtain ⟨c, hc, hcM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  have hv : β (∑ i, c i • b i) = 0 := by
    apply clm_eq_zero_of_basis b
    intro j
    rw [gram_apply_sum, hcM]
    rfl
  obtain ⟨e, he⟩ := h
  have h0' : (∑ i, c i • b i) = 0 := by
    apply e.injective
    rw [map_zero]
    rw [← he] at hv
    exact hv
  exact hc (funext fun i => Fintype.linearIndependent_iff.mp b.linearIndependent c h0' i)

theorem isInvertible_of_gram_ne_zero (b : Basis ι ℝ E) {β : E →L[ℝ] E →L[ℝ] ℝ}
    (h : gram b β ≠ 0) : β.IsInvertible := by
  have hI : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    apply h
    apply Matrix.exists_vecMul_eq_zero_iff.mp
    refine ⟨fun i => b.repr v i, ?_, ?_⟩
    · intro hz
      apply hne
      have : b.repr v = 0 := by
        ext i
        exact congrFun hz i
      simpa using this
    · funext j
      rw [← gram_apply_sum]
      simp [b.sum_repr v, hv]
  have hS : Function.Surjective β :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_continuous_dual (E := E)).symm).mp hI
  exact ⟨(LinearEquiv.ofBijective β.toLinearMap ⟨hI, hS⟩).toContinuousLinearEquiv, rfl⟩

theorem isInvertible_of_ndeg_pos (b : Basis ι ℝ E) {Γ : ℝ → ManifoldOneForm E E} {p : ℝ × E}
    (h : 0 < ndeg b Γ p) : (form Γ p).IsInvertible := by
  apply isInvertible_of_gram_ne_zero b
  intro h0
  simp [ndeg, h0] at h

/-! ### The Moser field -/

theorem mfield_eq {Γ : ℝ → ManifoldOneForm E E} {p : ℝ × E} (h : (form Γ p).IsInvertible) :
    mfield Γ p = -(form Γ p).inverse (tprim Γ p) := by
  obtain ⟨e, he⟩ := h
  have hv : form Γ p (-(form Γ p).inverse (tprim Γ p)) = -tprim Γ p := by
    rw [← he, ContinuousLinearMap.inverse_equiv]
    simp
  have hu : ∃! v : E, form Γ p v = -tprim Γ p := by
    refine ⟨_, hv, fun y hy => ?_⟩
    have h2 := hy.trans hv.symm
    rw [← he] at h2
    have h3 := e.injective h2
    rw [he] at h3
    exact h3
  unfold mfield
  rw [dif_pos hu]
  exact Explicit.the_eq hu hv

theorem moser_contDiffAt {Γ : ℝ → ManifoldOneForm E E} (hΓ : SmoothOneFormFamily Γ)
    {p : ℝ × E} (h : (form Γ p).IsInvertible) :
    ContDiffAt ℝ ∞ (fun q => -(form Γ q).inverse (tprim Γ q)) p := by
  obtain ⟨e, he⟩ := h
  have hg : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (form Γ p) :=
    he ▸ contDiffAt_map_inverse e
  exact ((hg.comp p (form_contDiff hΓ).contDiffAt).clm_apply
    (tprim_contDiff hΓ).contDiffAt).neg

/-! ### Properties of `lev`, `rad`, `cut` -/

theorem lev_nonneg (b : Basis ι ℝ E) (Γ : ℝ → ManifoldOneForm E E) (K : Set E) :
    0 ≤ lev b Γ K := by
  apply Real.sInf_nonneg
  rintro _ ⟨x, -, rfl⟩
  exact sq_nonneg _

theorem lev_le (b : Basis ι ℝ E) (Γ : ℝ → ManifoldOneForm E E) {K : Set E} {x : E}
    (hx : x ∈ K) : lev b Γ K ≤ ndeg b Γ (0, x) := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨y, -, rfl⟩
    exact sq_nonneg _
  · exact ⟨x, hx, rfl⟩

theorem lev_pos (b : Basis ι ℝ E) {Γ : ℝ → ManifoldOneForm E E} (hΓ : SmoothOneFormFamily Γ)
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    (hinv : ∀ x ∈ K, (manifoldExteriorOneForm (Γ 0) x).IsInvertible) : 0 < lev b Γ K := by
  have hc : Continuous fun x : E => ndeg b Γ (0, x) :=
    (ndeg_contDiff b hΓ).continuous.comp (continuous_const.prodMk continuous_id)
  have hmem := (hK.image hc).sInf_mem (hne.image _)
  obtain ⟨x, hx, hxe⟩ := hmem
  unfold lev
  rw [← hxe]
  have := gram_ne_zero_of_isInvertible b (hinv x hx)
  exact pow_pos_of_ne_zero' this
where
  pow_pos_of_ne_zero' {a : ℝ} (h : a ≠ 0) : 0 < a ^ 2 := by positivity

theorem qn_le_rad (b : Basis ι ℝ E) {K : Set E} (hK : IsCompact K) {x : E} (hx : x ∈ K) :
    qn b x ≤ rad b K :=
  le_csSup (hK.image (qn_contDiff b).continuous).bddAbove ⟨x, hx, rfl⟩

theorem cut_contDiff (b : Basis ι ℝ E) {Γ : ℝ → ManifoldOneForm E E} (hΓ : SmoothOneFormFamily Γ)
    (K : Set E) : ContDiff ℝ ∞ (cut b Γ K) := by
  have h1 : ContDiff ℝ ∞ fun p : ℝ × E => 4 * ndeg b Γ p / lev b Γ K - 2 :=
    ((contDiff_const.mul (ndeg_contDiff b hΓ)).div_const _).sub contDiff_const
  have h2 : ContDiff ℝ ∞ fun p : ℝ × E => 2 * (rad b K + 1 - qn b p.2) :=
    contDiff_const.mul (contDiff_const.sub ((qn_contDiff b).comp contDiff_snd))
  have h3 : ContDiff ℝ ∞ fun p : ℝ × E => 2 - p.1 ^ 2 :=
    contDiff_const.sub (contDiff_fst.pow 2)
  exact ((Real.smoothTransition.contDiff.comp h1).mul
    (Real.smoothTransition.contDiff.comp h2)).mul (Real.smoothTransition.contDiff.comp h3)

theorem cut_eq_one {b : Basis ι ℝ E} {Γ : ℝ → ManifoldOneForm E E} {K U : Set E}
    {A : ℝ × E → E} {T : Set E} {p : ℝ × E} (hp : p ∈ region b Γ K U A T) :
    cut b Γ K p = 1 := by
  obtain ⟨h1, h2, h3, -⟩ := hp
  simp [cut, Real.smoothTransition.one_of_one_le h1.le, Real.smoothTransition.one_of_one_le h2.le,
    Real.smoothTransition.one_of_one_le h3.le]

theorem ndeg_pos_of_region {b : Basis ι ℝ E} {Γ : ℝ → ManifoldOneForm E E} {K U : Set E}
    {A : ℝ × E → E} {T : Set E} {p : ℝ × E} (hp : p ∈ region b Γ K U A T) :
    0 < ndeg b Γ p := by
  obtain ⟨h1, -⟩ := hp
  rcases (sq_nonneg (gram b (form Γ p))).lt_or_eq with h | h
  · exact h
  · exfalso
    have h0 : ndeg b Γ p = 0 := h.symm
    rw [h0] at h1
    norm_num at h1

theorem cut_support {b : Basis ι ℝ E} {Γ : ℝ → ManifoldOneForm E E} {K : Set E} {p : ℝ × E}
    (hp : cut b Γ K p ≠ 0) : p.1 ^ 2 ≤ 2 ∧ qn b p.2 ≤ rad b K + 1 := by
  unfold cut at hp
  constructor
  · by_contra h
    apply hp
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2 - p.1 ^ 2 ≤ 0), mul_zero]
  · by_contra h
    apply hp
    rw [Real.smoothTransition.zero_of_nonpos (by linarith : 2 * (rad b K + 1 - qn b p.2) ≤ 0),
      mul_zero, zero_mul]

/-! ### Smoothness and compact support of the field -/

theorem field_contDiff (b : Basis ι ℝ E) {Γ : ℝ → ManifoldOneForm E E}
    (hΓ : SmoothOneFormFamily Γ) (K : Set E) : ContDiff ℝ ∞ (field b Γ K) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  by_cases hg : 0 < ndeg b Γ p
  · -- near `p` the form is invertible
    have hO : IsOpen {q : ℝ × E | 0 < ndeg b Γ q} :=
      isOpen_lt continuous_const (ndeg_contDiff b hΓ).continuous
    have he : (fun q => cut b Γ K q • -(form Γ q).inverse (tprim Γ q)) =ᶠ[𝓝 p] field b Γ K := by
      filter_upwards [hO.mem_nhds hg] with q hq
      simp only [field, mfield_eq (isInvertible_of_ndeg_pos b hq)]
    exact (((cut_contDiff b hΓ K).contDiffAt).smul
      (moser_contDiffAt hΓ (isInvertible_of_ndeg_pos b hg))).congr_of_eventuallyEq he.symm
  · -- `ndeg p = 0`: the cutoff vanishes near `p`
    have hp0 : ndeg b Γ p = 0 := le_antisymm (not_lt.mp hg) (sq_nonneg _)
    rcases (lev_nonneg b Γ K).lt_or_eq with hl | hl
    · have hO : IsOpen {q : ℝ × E | ndeg b Γ q < lev b Γ K / 2} :=
        isOpen_lt (ndeg_contDiff b hΓ).continuous continuous_const
      have hpO : p ∈ {q : ℝ × E | ndeg b Γ q < lev b Γ K / 2} := by
        show ndeg b Γ p < lev b Γ K / 2
        rw [hp0]; linarith
      have he : (fun _ => (0 : E)) =ᶠ[𝓝 p] field b Γ K := by
        filter_upwards [hO.mem_nhds hpO] with q hq
        have hq' : 4 * ndeg b Γ q / lev b Γ K - 2 ≤ 0 := by
          have : ndeg b Γ q / lev b Γ K < 1 / 2 := by
            rw [div_lt_iff₀ hl]; linarith [hq]
          have h4 : 4 * ndeg b Γ q / lev b Γ K = 4 * (ndeg b Γ q / lev b Γ K) := by ring
          linarith
        simp [field, cut, Real.smoothTransition.zero_of_nonpos hq']
      exact contDiffAt_const.congr_of_eventuallyEq he.symm
    · have he : field b Γ K = fun _ => 0 := by
        funext q
        simp [field, cut, ← hl, Real.smoothTransition.zero_of_nonpos (by norm_num : (-2 : ℝ) ≤ 0)]
      rw [he]
      exact contDiffAt_const

theorem field_eq_zero (b : Basis ι ℝ E) (Γ : ℝ → ManifoldOneForm E E) (K : Set E) (p : ℝ × E)
    (hp : ¬ (p.1 ^ 2 ≤ 2 ∧ qn b p.2 ≤ rad b K + 1)) : field b Γ K p = 0 := by
  by_cases hc : cut b Γ K p = 0
  · simp [field, hc]
  · exact absurd (cut_support hc) hp

theorem field_hasCompactSupport (b : Basis ι ℝ E) (Γ : ℝ → ManifoldOneForm E E) (K : Set E) :
    HasCompactSupport (field b Γ K) := by
  apply HasCompactSupport.intro ((isCompact_Icc (a := (-2 : ℝ)) (b := 2)).prod
    (isCompact_qn_le b (rad b K + 1)))
  intro p hp
  apply field_eq_zero
  rintro ⟨h1, h2⟩
  apply hp
  refine ⟨⟨?_, ?_⟩, h2⟩ <;> nlinarith [sq_nonneg (p.1 + 2), sq_nonneg (p.1 - 2)]

theorem field_lipschitz (b : Basis ι ℝ E) {Γ : ℝ → ManifoldOneForm E E}
    (hΓ : SmoothOneFormFamily Γ) (K : Set E) :
    ∃ C, ∀ t, LipschitzWith C (fun x => field b Γ K (t, x)) := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    (field_hasCompactSupport b Γ K) (field_contDiff b hΓ K) (by simp)
  refine ⟨C, fun t => ?_⟩
  have h := hC.comp (LipschitzWith.prodMk_left t)
  rw [mul_one] at h
  exact h

theorem tangent_smooth {V : ℝ × E → E} (hV : ContDiff ℝ ∞ V) :
    ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) (𝓘(ℝ, E)).tangent ∞
      (fun p : ℝ × E => (⟨p.2, V p⟩ : TangentBundle 𝓘(ℝ, E) E)) := by
  apply timeField_smooth_of_coordinates (V := fun p => V p)
  intro p
  have h : timeChartField (E := E) (M := E) (fun p => V p) p.2 = V := by
    funext q
    simp only [timeChartField, chartDifferential, extChartAt_model_space_eq_id,
      PartialEquiv.refl_coe, PartialEquiv.refl_symm, mfderiv_eq_fderiv, fderiv_id,
      ContinuousLinearMap.id_apply, id_eq]
  rw [h]
  exact hV.contDiffAt

/-! ### The flow -/

theorem curve_unique (b : Basis ι ℝ E) {Γ : ℝ → ManifoldOneForm E E}
    (hΓ : SmoothOneFormFamily Γ) (K : Set E) (x : E) {γ₁ γ₂ : ℝ → E}
    (h₁ : CurveP b Γ K x γ₁) (h₂ : CurveP b Γ K x γ₂) : γ₁ = γ₂ := by
  obtain ⟨C, hC⟩ := field_lipschitz b hΓ K
  have heq := ODE_solution_unique_of_mem_Ioo (v := fun t y => field b Γ K (t, y))
    (s := fun _ => univ) (K := C) (fun t _ => (hC t).lipschitzOnWith)
    (show (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 by norm_num)
    (fun t ht => ⟨h₁.2.1 t ht, mem_univ _⟩) (fun t ht => ⟨h₂.2.1 t ht, mem_univ _⟩)
    (h₁.1.trans h₂.1.symm)
  funext t
  by_cases ht : t ∈ Ioo (-2 : ℝ) 2
  · exact heq ht
  · rw [h₁.2.2 t ht, h₂.2.2 t ht]

/-- Comparison with any flow of `field` on `(-2, 2)`. -/
theorem flow_eq (b : Basis ι ℝ E) {Γ : ℝ → ManifoldOneForm E E}
    (hΓ : SmoothOneFormFamily Γ) (K : Set E) {Φ : ℝ × E → E} (hΦ0 : ∀ x, Φ (0, x) = x)
    (hODE : ∀ x t, t ∈ Ioo (-2 : ℝ) 2 →
      HasDerivAt (fun s => Φ (s, x)) (field b Γ K (t, Φ (t, x))) t)
    {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) (x : E) : flow b Γ K (t, x) = Φ (t, x) := by
  classical
  let γ : ℝ → E := fun s => if s ∈ Ioo (-2 : ℝ) 2 then Φ (s, x) else x
  have hγ : CurveP b Γ K x γ := by
    refine ⟨?_, ?_, ?_⟩
    · show (if (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 then Φ (0, x) else x) = x
      rw [if_pos (show (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 from ⟨by norm_num, by norm_num⟩), hΦ0]
    · intro s hs
      have he : (fun r => Φ (r, x)) =ᶠ[𝓝 s] γ := by
        filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
        exact (if_pos hr).symm
      have hd := (hODE x s hs).congr_of_eventuallyEq he.symm
      have hγs : γ s = Φ (s, x) := if_pos hs
      rw [hγs]
      exact hd
    · intro s hs
      exact if_neg hs
  have hu : ∃! γ, CurveP b Γ K x γ := ⟨γ, hγ, fun γ' h' => curve_unique b hΓ K x h' hγ⟩
  have hc : curve b Γ K x = γ := by
    unfold curve
    rw [dif_pos hu]
    exact Explicit.the_eq hu hγ
  show curve b Γ K x t = Φ (t, x)
  rw [hc]
  exact if_pos ht

/-! ### The main theorem -/

theorem region_isOpen (b : Basis ι ℝ E) {Γ : ℝ → ManifoldOneForm E E}
    (hΓ : SmoothOneFormFamily Γ) (K : Set E) {U : Set E} (hU : IsOpen U) {A : ℝ × E → E}
    (hA : Continuous A) {T : Set E} (hT : IsOpen T) : IsOpen (region b Γ K U A T) := by
  have hn := (ndeg_contDiff b hΓ).continuous
  have hq := (qn_contDiff b).continuous
  refine (isOpen_lt continuous_const ((continuous_const.mul hn).div_const _ |>.sub
    continuous_const)).inter ((isOpen_lt continuous_const (continuous_const.mul
    (continuous_const.sub (hq.comp continuous_snd)))).inter ((isOpen_lt continuous_const
    (continuous_const.sub (continuous_fst.pow 2))).inter ((hU.preimage continuous_snd).inter
    (hT.preimage hA))))

theorem guards_contDiff {n : ℕ} (b : Basis ι ℝ E)
    {Γ : ℝ → ManifoldOneForm E E} (hΓ : SmoothOneFormFamily Γ) (K : Set E)
    {g : Fin n → ℝ × E → ℝ} (hg : ∀ i, ContDiff ℝ ∞ (g i)) :
    ∀ i, ContDiff ℝ ∞ (guards b Γ K g i) := by
  apply Fin.addCases
  · intro i
    fin_cases i <;> simp only [guards, Fin.addCases_left, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_fin_one]
    · exact ((contDiff_const.mul (ndeg_contDiff b hΓ)).div_const _).sub contDiff_const
    · exact (contDiff_const.mul (contDiff_const.sub ((qn_contDiff b).comp contDiff_snd))).sub contDiff_const
    · exact contDiff_const.sub (contDiff_fst.pow 2)
  · intro i
    have he : guards b Γ K g (Fin.natAdd 3 i) = g i := by
      funext p
      simp [guards]
    rw [he]
    exact hg i

lemma guards_positive_iff {n : ℕ} (b : Basis ι ℝ E)
    (Γ : ℝ → ManifoldOneForm E E) (K : Set E) (g : Fin n → ℝ × E → ℝ) (p : ℝ × E) :
    (∀ i, 0 < guards b Γ K g i p) ↔
      (1 < 4*ndeg b Γ p/lev b Γ K-2 ∧
       1 < 2*(rad b K+1-qn b p.2) ∧ 1 < 2-p.1^2) ∧ ∀ i, 0<g i p := by
  rw [Fin.forall_fin_add]
  simp only [guards, Fin.addCases_left, Fin.addCases_right, Fin.forall_fin_succ,
    Fin.val_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.forall_fin_zero,
    forall_true_left, and_true]
  constructor <;> intro h
  · exact ⟨⟨by linarith [h.1.1], by linarith [h.1.2.1], by linarith [h.1.2.2]⟩,h.2⟩
  · exact ⟨⟨by linarith [h.1.1], by linarith [h.1.2.1], by linarith [h.1.2.2]⟩,h.2⟩

set_option maxHeartbeats 1600000 in
theorem spec (b : Basis ι ℝ E) {Γ : ℝ → ManifoldOneForm E E}
    (hΓ : SmoothOneFormFamily Γ) {K : Set E} (hK : IsCompact K)
    (hinv : ∀ x ∈ K, (manifoldExteriorOneForm (Γ 0) x).IsInvertible)
    {U : Set E} (hU : IsOpen U) (hKU : K ⊆ U)
    {δ : ℝ} (hδ : 0 < δ) {A : ℝ × E → E}
    (hA : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E)) 𝓘(ℝ, E) ∞ A)
    (hemb : ∀ t ∈ Ioc (0 : ℝ) δ, Topology.IsEmbedding (fun x : U => A (t, x.val)))
    {T : Set E} (hT : IsOpen T) (hinto : MapsTo (fun x => A (0, x)) K T)
    {n : ℕ} (g : Fin n → ℝ × E → ℝ)
    (hgs : ∀ i, ContDiff ℝ ∞ (g i))
    (hg0 : ∀ i, ∀ x ∈ K, 0 < g i (0,x))
    (hge : ∀ p, (∀ i, 0 < g i p) → p.2 ∈ U ∧ A p ∈ T)
    (Ω : ℝ → ManifoldTwoForm E E)
    (hform : ∀ t ∈ Ioc (0 : ℝ) δ, ∀ x ∈ U,
      manifoldExteriorOneForm (Γ t) x = (Ω t (A (t, x))).bilinearComp
        (manifoldMapDifferential (E := E) (F := E) (fun y => A (t, y)) x)
        (manifoldMapDifferential (E := E) (F := E) (fun y => A (t, y)) x)) :
    let τ := time b Γ K δ g
    0 < τ ∧ τ ≤ δ ∧ ∀ t ∈ Ioc (0 : ℝ) τ, ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (map b Γ K A t) ∧
      Topology.IsEmbedding (fun x : W => map b Γ K A t x.val) ∧
      MapsTo (map b Γ K A t) W T ∧ ∀ x ∈ W, ∀ v w, Ω t (map b Γ K A t x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (map b Γ K A t) x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (map b Γ K A t) x w) =
          manifoldExteriorOneForm (Γ 0) x v w := by
  intro τ
  -- the OpenAI flow of the explicit field
  have hV := tangent_smooth (field_contDiff b hΓ K)
  obtain ⟨Φ, Ψ, hΦ, hΨ, hΦ0, hΦi, hODE, -⟩ :=
    exists_spatially_compact_nonautonomous_flow hV
      (isCompact_qn_le b (rad b K + 1)) (fun s x hx => field_eq_zero b Γ K (s, x)
        (fun h => hx h.2))
  have hODE' : ∀ x t, t ∈ Ioo (-2 : ℝ) 2 →
      HasDerivAt (fun s => Φ (s, x)) (field b Γ K (t, Φ (t, x))) t := by
    intro x t ht
    have h := hODE x t ht
    exact hasDerivAt_iff_hasFDerivAt.mpr (hasMFDerivAt_iff_hasFDerivAt.mp h)
  have hfl : ∀ t ∈ Ioo (-2 : ℝ) 2, ∀ x, flow b Γ K (t, x) = Φ (t, x) :=
    fun t ht x => flow_eq b hΓ K hΦ0 hODE' ht x
  have hAc : Continuous A := hA.continuous
  let R := region b Γ K U A T
  have hR : IsOpen R := region_isOpen b hΓ K hU hAc hT
  let P : Set (ℝ × E) := {p | (p.1, Φ p) ∈ R}
  have hP : IsOpen P := hR.preimage (continuous_fst.prodMk hΦ.continuous)
  -- the time-zero slice lies in the region
  have h0R : ∀ x ∈ K, ((0 : ℝ), x) ∈ R := by
    intro x hx
    have hl := lev_pos b hΓ hK ⟨x, hx⟩ hinv
    have hlx := lev_le b Γ hx
    have hqx := qn_le_rad b hK hx
    refine ⟨?_, ?_, ?_, hKU hx, hinto hx⟩
    · have : 1 ≤ ndeg b Γ (0, x) / lev b Γ K := by rw [le_div_iff₀ hl]; linarith
      have : 4 * ndeg b Γ (0, x) / lev b Γ K = 4 * (ndeg b Γ (0, x) / lev b Γ K) := by ring
      linarith
    · linarith
    · norm_num
  -- Finite guards along the complete cutoff flow.
  let f : Fin (3+n) → ℝ × E → ℝ :=
    fun i p => guards b Γ K g i (p.1,flow b Γ K p)
  have hΦc : ContDiff ℝ ∞ Φ := by
    have hh := hΦ
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hh
    exact hh.contDiff
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (Ioo (-2:ℝ) 2 ×ˢ univ) := by
    intro i
    apply ((guards_contDiff b hΓ K hgs i).comp
      (contDiff_fst.prodMk hΦc)).contDiffOn.congr
    intro p hp
    exact congrArg (guards b Γ K g i) (Prod.ext rfl (hfl p.1 hp.1 p.2))
  have hfm : ∀ i, ContMDiffOn ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ (f i)
      (Ioo (-2:ℝ) 2 ×ˢ univ) := by
    intro i
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
    exact (hf i).contMDiffOn
  have h0 : ∀ i, ContinuousOn (fun x => f i (0,x)) K := by
    intro i x hx
    have hfx := (hf i (0,x) ⟨by norm_num,mem_univ _⟩).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨by norm_num,mem_univ _⟩)
    exact (hfx.continuousAt.comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
  have hd := fun i => ExactSafety.time_derivative_continuousOn (K:=K) (hfm i)
  have hder : ∀ i, ∀ x∈K, ∀ s∈Icc (-1:ℝ) 1,
      DifferentiableAt ℝ (fun r => f i (r,x)) s := by
    intro i x hx s hs
    have hsO : (s,x) ∈ Ioo (-2:ℝ) 2 ×ˢ (univ:Set E) :=
      ⟨⟨by linarith [hs.1],by linarith [hs.2]⟩,mem_univ _⟩
    exact (((hf i (s,x) hsO).contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds hsO)).comp s
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
  have hpos : ∀ i, ∀ x∈K, 0<f i (0,x) := by
    intro i x hx
    have he : flow b Γ K (0,x) = x := by rw [hfl 0 (by norm_num) x,hΦ0]
    change 0 < guards b Γ K g i (0,flow b Γ K (0,x))
    rw [he]
    exact (guards_positive_iff b Γ K g (0,x)).mpr
      ⟨⟨(h0R x hx).1,(h0R x hx).2.1,(h0R x hx).2.2.1⟩,fun j => hg0 j x hx⟩ i
  have hc := ExactSafety.clearance_pos hK h0 hpos
  have hv := ExactSafety.speed_pos hK hd
  have hτpos : 0<τ := ExactSafety.time_pos hc hv hδ
  have hτb := ExactSafety.time_bounds f K δ
  have hstayK : ∀ s∈Icc (0:ℝ) τ, ∀ x∈K,
      (s,flow b Γ K (s,x)) ∈ R := by
    intro s hs x hx
    have hgp : ∀ i, 0<f i (s,x) := by
      intro i
      have habs : |s|≤2*ExactSafety.time f K δ := by
        rw [abs_of_nonneg hs.1]
        change s≤2*τ
        linarith [hs.2]
      have hh := ExactSafety.guard_ge_half hK h0 hd hder hpos hδ i hx habs
      linarith
    have hh := (guards_positive_iff b Γ K g (s,flow b Γ K (s,x))).mp hgp
    exact ⟨hh.1.1,hh.1.2.1,hh.1.2.2,(hge _ hh.2).1,(hge _ hh.2).2⟩
  refine ⟨hτpos, by change ExactSafety.time f K δ ≤ δ; linarith [hτb.1], ?_⟩
  intro t ht
  have htt : t ≤ ExactSafety.time f K δ := ht.2
  have ht1 : t ≤ 1 := by linarith [htt,hτb.2.1]
  have htδ : t ≤ δ := by linarith [htt,hτb.1]
  have ht0 : 0<t := ht.1
  have hIoo : ∀ s ∈ Icc (0 : ℝ) t, s ∈ Ioo (-2 : ℝ) 2 :=
    fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  -- an open neighbourhood `W` of `K` whose flow lines stay in the region up to time `t`
  obtain ⟨V', W, -, hWo, hIV', hKW, hVW'⟩ := generalized_tube_lemma (isCompact_Icc (a := (0 : ℝ))
    (b := t)) hK hP (by
      rintro ⟨s, x⟩ ⟨hs, hx⟩
      have h := hstayK s ⟨hs.1, hs.2.trans ht.2⟩ x hx
      rw [hfl s (hIoo s hs) x] at h
      exact h)
  have hstay : ∀ s ∈ Icc (0 : ℝ) t, ∀ x ∈ W, (s, Φ (s, x)) ∈ R :=
    fun s hs x hx => by
      have hmem : (s, x) ∈ P := hVW' (Set.mk_mem_prod (hIV' hs) hx)
      exact hmem
  have hmap : map b Γ K A t = fun x => A (t, Φ (t, x)) := by
    funext x
    simp only [map, hfl t (hIoo t ⟨ht0.le, le_rfl⟩) x]
  -- the Moser identity along the flow
  let O : Set (ℝ × E) := {p | 1 < 4 * ndeg b Γ p / lev b Γ K - 2 ∧
    1 < 2 * (rad b K + 1 - qn b p.2) ∧ 1 < 2 - p.1 ^ 2}
  have hO : IsOpen O := by
    have hn := (ndeg_contDiff b hΓ).continuous
    have hq := (qn_contDiff b).continuous
    exact (isOpen_lt continuous_const ((continuous_const.mul hn).div_const _ |>.sub
      continuous_const)).inter ((isOpen_lt continuous_const (continuous_const.mul
      (continuous_const.sub (hq.comp continuous_snd)))).inter (isOpen_lt continuous_const
      (continuous_const.sub (continuous_fst.pow 2))))
  have hOR : ∀ p ∈ O, p ∈ region b Γ K univ (fun _ => (0 : E)) univ :=
    fun p hp => ⟨hp.1, hp.2.1, hp.2.2, mem_univ _, mem_univ _⟩
  have hOinv : ∀ p ∈ O, (manifoldExteriorOneForm (Γ p.1) p.2).IsInvertible :=
    fun p hp => isInvertible_of_ndeg_pos b (ndeg_pos_of_region (hOR p hp))
  have hOeq : ∀ p ∈ O, field b Γ K p = manifoldMoserField
      (fun t => manifoldExteriorOneForm (Γ t)) (manifoldTimePrimitive Γ) p := by
    intro p hp
    rw [field, cut_eq_one (hOR p hp), one_smul, mfield_eq (hOinv p hp)]
    rfl
  have hd : ∀ s ∈ Icc (0 : ℝ) t, ∀ x ∈ W, ∀ v w : E,
      HasDerivAt (fun r => manifoldPullback Φ (fun r => manifoldExteriorOneForm (Γ r)) r x v w)
        0 s := by
    intro s hs x hx v w
    have hsR := hstay s hs x hx
    exact exact_path_local_transport_derivative hΓ hΦ hV hODE hO hOinv hOeq (hIoo s hs)
      ⟨hsR.1, hsR.2.1, hsR.2.2.1⟩ v w
  have hconst : ∀ x ∈ W, ∀ v w : E,
      manifoldPullback Φ (fun r => manifoldExteriorOneForm (Γ r)) t x v w =
        manifoldExteriorOneForm (Γ 0) x v w := by
    intro x hx v w
    have he := (convex_Icc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s hs => (hd s hs x hx v w).hasDerivWithinAt)
      (fun _ _ => (by simp : ‖(0 : ℝ)‖ ≤ (0 : ℝ)))
      (show (0 : ℝ) ∈ Icc (0 : ℝ) t from ⟨le_rfl, ht0.le⟩) ⟨ht0.le, le_rfl⟩
    have he' : manifoldPullback Φ (fun r => manifoldExteriorOneForm (Γ r)) t x v w =
        manifoldPullback Φ (fun r => manifoldExteriorOneForm (Γ r)) 0 x v w := by
      simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using he
    rw [he']
    have hid : (fun y => Φ (0, y)) = id := funext hΦ0
    have hD : preferredDifferential (fun y => Φ (0, y)) x = ContinuousLinearMap.id ℝ E := by
      change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y => Φ (0, y)) x = _
      rw [hid]
      exact mfderiv_id
    rw [manifoldPullback, hD]
    simp only [hΦ0, ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.id_apply]
  -- the embedding and the form identity
  have hφ := hΦ.comp (contMDiff_const.prodMk contMDiff_id) (f := fun x : E => (t, x))
  have hψ := hΨ.comp (contMDiff_const.prodMk contMDiff_id) (f := fun x : E => (t, x))
  have hφemb : Topology.IsEmbedding (fun x : E => Φ (t, x)) := by
    apply Topology.IsEmbedding.of_comp hφ.continuous hψ.continuous
    have he : (fun x : E => Ψ (t, Φ (t, x))) = id :=
      funext fun x => (hΦi t ⟨ht0.le, ht1⟩ x).1
    change Topology.IsEmbedding (fun x : E => Ψ (t, Φ (t, x)))
    rw [he]
    exact Topology.IsEmbedding.id
  have ha := hA.comp (contMDiff_const.prodMk contMDiff_id) (f := fun x : E => (t, x))
  have hWU : ∀ x ∈ W, Φ (t, x) ∈ U := fun x hx => (hstay t ⟨ht0.le, le_rfl⟩ x hx).2.2.2.1
  rw [hmap]
  refine ⟨W, hWo, hKW, ha.comp hφ, ?_, ?_, ?_⟩
  · exact (hemb t ⟨ht0, htδ⟩).comp
      ((hφemb.comp Topology.IsEmbedding.subtypeVal).codRestrict U
        (fun x : W => hWU x.val x.property))
  · intro x hx
    exact (hstay t ⟨ht0.le, le_rfl⟩ x hx).2.2.2.2
  · intro x hx v w
    have hd' := mfderiv_comp x (ha.mdifferentiable (by simp) (Φ (t, x)))
      (hφ.mdifferentiable (by simp) x)
    change Ω t (A (t, Φ (t, x)))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((A ∘ fun y => (t, y)) ∘ (Φ ∘ fun y => (t, y))) x v)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((A ∘ fun y => (t, y)) ∘ (Φ ∘ fun y => (t, y))) x w) = _
    rw [hd']
    have hf := congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ =>
      B (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y => Φ (t, y)) x v)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun y => Φ (t, y)) x w))
      (hform t ⟨ht0, htδ⟩ (Φ (t, x)) (hWU x hx))
    exact hf.symm.trans (hconst x hx v w)

end SymplecticPacking.BranchLarge3.UMoser
