import SymplecticPacking.HighDim.Handle.QuadricTightAmbientBoxes
import SymplecticPacking.HighDim.Handle.RawRationalBoxBasis
import SymplecticPacking.Effective.AlgebraicComplex

/-!
# Overlap certificates for the quadric charts

Finite scalar overlap certificates for the explicit diagonal-quadric charts.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function Complex Filter
open scoped Topology ComplexConjugate
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.Hamiltonian

/-- All ambient complex coordinates, with `none` denoting the base coordinate. -/
def quadricCoordinate {m : ℕ} {a : Fin m → ℂ} (x : locus a) : Option (Fin m) → ℂ
  | none => x.val.1
  | some j => x.val.2 j

lemma quadricCoordinate_continuous {m : ℕ} {a : Fin m → ℂ} (i : Option (Fin m)) :
    Continuous (fun x : locus a => quadricCoordinate x i) := by
  cases i <;> unfold quadricCoordinate <;> fun_prop

lemma quadricCoordinate_square_difference {m : ℕ} {a : Fin m → ℂ}
    (x y : locus a) (i j : Option (Fin m)) :
    quadricCoordinate x i ^ 2 - quadricCoordinate y i ^ 2 =
      quadricCoordinate x j ^ 2 - quadricCoordinate y j ^ 2 := by
  have he (z : locus a) (k : Option (Fin m)) :
      quadricCoordinate z k ^ 2 = z.val.1 ^ 2 - k.elim 0 a := by
    cases k with
    | none => simp [quadricCoordinate]
    | some k => exact mem_locus.mp z.property k
  rw [he, he, he, he]
  ring

/-- The root difference estimate uses the prescribed open half-plane, rather than a
supremum of derivatives or an unspecified root branch. -/
lemma root_difference_bound {c w v : ℂ} {K : ℝ} (hc : c ≠ 0) (hK : 0 ≤ K)
    (hw : 0 ≤ (w * conj c).re) (hv : ‖c‖ ≤ K * (v * conj c).re) :
    ‖w - v‖ ≤ K * ‖w ^ 2 - v ^ 2‖ := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hs : (v * conj c).re ≤ ‖w + v‖ * ‖c‖ := by
    calc
      (v * conj c).re ≤ (w * conj c).re + (v * conj c).re := by linarith
      _ = ((w + v) * conj c).re := by rw [add_mul, Complex.add_re]
      _ ≤ ‖(w + v) * conj c‖ := Complex.re_le_norm _
      _ = ‖w + v‖ * ‖c‖ := by rw [norm_mul, norm_conj]
  have hm := hv.trans (mul_le_mul_of_nonneg_left hs hK)
  have hunit : 1 ≤ K * ‖w + v‖ := by
    have hh : ‖c‖ ≤ (K * ‖w + v‖) * ‖c‖ := by simpa only [mul_assoc] using hm
    by_contra hn
    have ht := mul_lt_mul_of_pos_right (not_le.mp hn) hcpos
    linarith only [hh, ht]
  have hfactor : ‖w ^ 2 - v ^ 2‖ = ‖w - v‖ * ‖w + v‖ := by
    rw [← norm_mul]
    congr 1
    ring
  rw [hfactor]
  calc
    ‖w-v‖ = ‖w-v‖ * 1 := by ring
    _ ≤ ‖w-v‖ * (K * ‖w+v‖) := mul_le_mul_of_nonneg_left hunit (norm_nonneg _)
    _ = K * (‖w-v‖ * ‖w+v‖) := by ring

/-- Only the fixed algebraic centre and the choice of free coordinate are data. -/
structure QuadricRootChart {m : ℕ} (a : Fin m → ℂ) where
  centre : locus a
  tag : Option (Fin m)
  regular : centre.val ∈ regularCoordinate tag

namespace QuadricRootChart
variable {m : ℕ} {a : Fin m → ℂ}

def chart : QuadricRootChart a → OpenPartialHomeomorph (locus a) Plane
  | ⟨c, none, hc⟩ => ordinaryRealExplicitChart c hc
  | ⟨c, some i, hc⟩ => branchRealExplicitChart c i hc

lemma chart_apply (C : QuadricRootChart a) (x : locus a) :
    C.chart x = Complex.equivRealProdCLM (quadricCoordinate x C.tag) := by
  rcases C with ⟨c, tag, hc⟩
  cases tag <;> rfl

lemma chart_continuous (C : QuadricRootChart a) : Continuous C.chart := by
  have he : (C.chart : locus a → Plane) = fun x => Complex.equivRealProdCLM (quadricCoordinate x C.tag) :=
    funext (C.chart_apply)
  rw [he]
  exact Complex.equivRealProdCLM.continuous.comp (quadricCoordinate_continuous C.tag)

lemma centre_ne_zero (C : QuadricRootChart a) {i : Option (Fin m)} (hi : i ≠ C.tag) :
    quadricCoordinate C.centre i ≠ 0 := by
  rcases C with ⟨c, tag, hc⟩
  cases tag with
  | none =>
      cases i with
      | none => exact (hi rfl).elim
      | some j => exact hc j
  | some k =>
      cases i with
      | none => exact hc.1
      | some j => exact hc.2 j (fun hj => hi (congrArg some hj))

lemma mul_conj_re_pos_of_div {z c : ℂ} (hc : c ≠ 0) (h : 0 < (z / c).re) :
    0 < (z * conj c).re := by
  rw [Complex.div_re, ← add_div] at h
  have hsq : 0 < Complex.normSq c := Complex.normSq_pos.mpr hc
  have hh := (div_pos_iff_of_pos_right hsq).mp h
  simpa [Complex.mul_re] using hh

lemma div_re_pos_of_mul_conj {z c : ℂ} (hc : c ≠ 0) (h : 0 < (z * conj c).re) :
    0 < (z / c).re := by
  rw [Complex.div_re, ← add_div]
  have hh : 0 < z.re * c.re + z.im * c.im := by simpa [Complex.mul_re] using h
  exact div_pos hh (Complex.normSq_pos.mpr hc)

lemma source_positive (C : QuadricRootChart a) {x : locus a} (hx : x ∈ C.chart.source)
    {i : Option (Fin m)} (hi : i ≠ C.tag) :
    0 < (quadricCoordinate x i * conj (quadricCoordinate C.centre i)).re := by
  apply mul_conj_re_pos_of_div (C.centre_ne_zero hi)
  rcases C with ⟨c, tag, hc⟩
  cases tag with
  | none =>
      have hx₀ : x ∈ ordinaryLocalSource c := hx.1
      cases i with
      | none => exact (hi rfl).elim
      | some j => exact hx₀.2 j
  | some k =>
      have hx₀ : x ∈ branchLocalSource c k := hx.1
      cases i with
      | none => exact hx₀.2.1
      | some j => exact hx₀.2.2 j (fun hj => hi (congrArg some hj))

lemma source_of_target_positive (C : QuadricRootChart a) {x : locus a}
    (ht : C.chart x ∈ C.chart.target)
    (hs : ∀ i, i ≠ C.tag →
      0 < (quadricCoordinate x i * conj (quadricCoordinate C.centre i)).re) :
    x ∈ C.chart.source := by
  have hp (i : Option (Fin m)) (hi : i ≠ C.tag) :
      0 < (quadricCoordinate x i / quadricCoordinate C.centre i).re :=
    div_re_pos_of_mul_conj (C.centre_ne_zero hi) (hs i hi)
  rcases C with ⟨c, tag, hc⟩
  cases tag with
  | none =>
      refine ⟨⟨ht.2, ?_⟩, mem_univ _⟩
      intro j
      exact hp (some j) (by simp)
  | some k =>
      refine ⟨⟨ht.2, hp none (by simp), ?_⟩, mem_univ _⟩
      intro j hj
      exact hp (some j) (by simpa using hj)

/-- A finite collection of centre half-plane bounds controls every ambient coordinate
of the inverse chart on a closed coordinate disc. -/
lemma coordinate_variation_bound (C : QuadricRootChart a) {x y : locus a}
    (hx : x ∈ C.chart.source) {δ K : ℝ} (hK : 0 ≤ K)
    (hδ : quadricCoordinate x C.tag ∈ Metric.closedBall (quadricCoordinate y C.tag) δ)
    (hbound : ∀ i, i ≠ C.tag → ‖quadricCoordinate C.centre i‖ ≤
      K * (quadricCoordinate y i * conj (quadricCoordinate C.centre i)).re)
    (i : Option (Fin m)) :
    ‖quadricCoordinate x i - quadricCoordinate y i‖ ≤
      max δ (K * (δ * (2 * ‖quadricCoordinate y C.tag‖ + δ))) := by
  by_cases hi : i = C.tag
  · subst i
    exact (show ‖quadricCoordinate x C.tag - quadricCoordinate y C.tag‖ ≤ δ from
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hδ)).trans (le_max_left _ _)
  · apply le_trans _ (le_max_right _ _)
    have hh := root_difference_bound (C.centre_ne_zero hi) hK
      (C.source_positive hx hi).le (hbound i hi)
    rw [quadricCoordinate_square_difference x y i C.tag] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (norm_square_difference_le hδ) hK)

/-- A closed coordinate disc inside an original coordinate ball is a formula box
in the very same chart. No inclusion oracle enters its definition. -/
def offsetBox (C : QuadricRootChart a) (B : RawCoordinateBox (locus a))
    (hB : B.chart = C.chart) (q : ℚ × ℚ) (r : ℚ) (hr : 0 < (r:ℝ))
    (hinside : dist (rationalPlane q) B.point + (r:ℝ) < B.radius) :
    RawCoordinateBox (locus a) where
  chart := C.chart
  point := rationalPlane q
  radius := r
  radius_pos := hr
  closed_subset := by
    intro z hz
    rw [← hB]
    apply B.closed_subset
    rw [Metric.mem_closedBall]
    have hh := dist_triangle z (rationalPlane q) B.point
    have hz' : dist z (rationalPlane q) ≤ (r:ℝ) := hz
    linarith

lemma offsetBox_compactCarrier_subset (C : QuadricRootChart a)
    (B : RawCoordinateBox (locus a)) (hB : B.chart = C.chart)
    (q : ℚ × ℚ) (r : ℚ) (hr : 0 < (r:ℝ))
    (hinside : dist (rationalPlane q) B.point + (r:ℝ) < B.radius) :
    (C.offsetBox B hB q r hr hinside).compactCarrier ⊆ B.carrier := by
  rintro x ⟨z, hz, rfl⟩
  have hzin : z ∈ B.chart.target := by
    rw [hB]
    exact (C.offsetBox B hB q r hr hinside).closed_subset hz
  refine ⟨?_, ?_⟩
  · change C.chart.symm z ∈ B.chart.source
    rw [hB]
    exact C.chart.map_target (hB ▸ hzin)
  · change B.chart (C.chart.symm z) ∈ Metric.ball B.point B.radius
    rw [hB, C.chart.right_inv (hB ▸ hzin)]
    rw [Metric.mem_ball]
    have hh := dist_triangle z (rationalPlane q) B.point
    have hz' : dist z (rationalPlane q) ≤ (r:ℝ) := hz
    linarith

lemma chart_dist_le (C : QuadricRootChart a) (x y : locus a) :
    dist (C.chart x) (C.chart y) ≤
      ‖quadricCoordinate x C.tag - quadricCoordinate y C.tag‖ := by
  rw [C.chart_apply, C.chart_apply, dist_eq_norm, ← map_sub]
  rw [Prod.norm_def]
  change max |(quadricCoordinate x C.tag - quadricCoordinate y C.tag).re|
    |(quadricCoordinate x C.tag - quadricCoordinate y C.tag).im| ≤ _
  exact max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)

lemma halfplane_positive_of_close {z w c : ℂ} {d : ℝ}
    (hd : ‖z-w‖ ≤ d) (h : d * ‖c‖ < (w * conj c).re) :
    0 < (z * conj c).re := by
  have hn : (w * conj c).re - (z * conj c).re ≤ d * ‖c‖ := by
    calc
      (w * conj c).re - (z * conj c).re = ((w-z) * conj c).re := by
        rw [sub_mul, Complex.sub_re]
      _ ≤ ‖(w-z) * conj c‖ := Complex.re_le_norm _
      _ = ‖z-w‖ * ‖c‖ := by rw [norm_mul, norm_conj, norm_sub_rev]
      _ ≤ d * ‖c‖ := mul_le_mul_of_nonneg_right hd (norm_nonneg _)
  linarith

/-- The additional rational `K` is a bound for the finitely many root secants. -/
structure OverlapCode where
  point : ℚ × ℚ
  radius : ℚ
  bound : ℚ
  deriving Encodable

def variationFactor (q : ℚ × ℚ) (K : ℚ) : ℚ :=
  1 + K * (2 * (|q.1| + |q.2|) + 2)

/-- Every test is a scalar strict inequality at the displayed rational coordinate.
This geometric predicate deliberately has no classical real-order decision instance. -/
structure OverlapValid (C E : QuadricRootChart a) (B A : RawCoordinateBox (locus a))
    (code : OverlapCode) : Prop where
  radius_pos : 0 < (code.radius : ℝ)
  radius_lt_one : (code.radius : ℝ) < 1
  bound_gt_one : 1 < (code.bound : ℝ)
  inside : dist (rationalPlane code.point) B.point + (code.radius : ℝ) < B.radius
  secants : ∀ i, i ≠ C.tag → ‖quadricCoordinate C.centre i‖ <
    (code.bound : ℝ) * (quadricCoordinate (C.chart.symm (rationalPlane code.point)) i *
      conj (quadricCoordinate C.centre i)).re
  signs : ∀ i, i ≠ E.tag →
    2 * (code.radius : ℝ) * (variationFactor code.point code.bound : ℝ) *
        ‖quadricCoordinate E.centre i‖ <
      (quadricCoordinate (C.chart.symm (rationalPlane code.point)) i *
        conj (quadricCoordinate E.centre i)).re
  coordinate : dist (E.chart (C.chart.symm (rationalPlane code.point))) A.point +
    2 * (code.radius : ℝ) * (variationFactor code.point code.bound : ℝ) < A.radius

lemma variationFactor_pos (q : ℚ × ℚ) {K : ℚ} (hK : 0 ≤ (K:ℝ)) :
    1 ≤ (variationFactor q K : ℝ) := by
  simp only [variationFactor, Rat.cast_add, Rat.cast_mul, Rat.cast_one, Rat.cast_ofNat, Rat.cast_abs]
  have hh : 0 ≤ (K:ℝ) * (2 * (|(q.1:ℝ)| + |(q.2:ℝ)|) + 2) := mul_nonneg hK (by positivity)
  linarith

lemma coordinate_disc_bound (C : QuadricRootChart a) {x y : locus a} (hx : x ∈ C.chart.source)
    (q : ℚ × ℚ) {r K : ℚ} (hr : 0 < (r:ℝ)) (hr₁ : (r:ℝ) < 1) (hK : 0 ≤ (K:ℝ))
    (hy : C.chart y = rationalPlane q)
    (hδ : quadricCoordinate x C.tag ∈ Metric.closedBall (quadricCoordinate y C.tag) (2*(r:ℝ)))
    (hb : ∀ i, i ≠ C.tag → ‖quadricCoordinate C.centre i‖ ≤
      (K:ℝ) * (quadricCoordinate y i * conj (quadricCoordinate C.centre i)).re)
    (i : Option (Fin m)) :
    ‖quadricCoordinate x i - quadricCoordinate y i‖ ≤
      2 * (r:ℝ) * (variationFactor q K : ℝ) := by
  have hq : quadricCoordinate y C.tag = Complex.equivRealProdCLM.symm (rationalPlane q) := by
    rw [C.chart_apply] at hy
    apply Complex.equivRealProdCLM.injective
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact hy
  have hnorm : ‖quadricCoordinate y C.tag‖ ≤ |(q.1:ℝ)| + |(q.2:ℝ)| := by
    rw [hq]
    exact Complex.norm_le_abs_re_add_abs_im _
  apply (C.coordinate_variation_bound hx hK hδ hb i).trans
  apply max_le
  · have hL := mul_le_mul_of_nonneg_left (variationFactor_pos q hK)
      (by positivity : 0 ≤ 2*(r:ℝ))
    simpa only [mul_one] using hL
  · have hm : 2 * ‖quadricCoordinate y C.tag‖ + 2 * (r:ℝ) ≤
        2 * (|(q.1:ℝ)| + |(q.2:ℝ)|) + 2 := by linarith
    have hp := mul_le_mul_of_nonneg_left hm (mul_nonneg hK (by positivity : 0 ≤ 2*(r:ℝ)))
    simp only [variationFactor, Rat.cast_add, Rat.cast_mul, Rat.cast_one, Rat.cast_ofNat,
      Rat.cast_abs]
    nlinarith only [hp, hr]

lemma exists_secant_bound (C : QuadricRootChart a) {x : locus a} (hx : x ∈ C.chart.source) :
    ∃ K : ℚ, 1 < (K:ℝ) ∧ ∀ i, i ≠ C.tag → ‖quadricCoordinate C.centre i‖ <
      (K:ℝ) * (quadricCoordinate x i * conj (quadricCoordinate C.centre i)).re := by
  classical
  obtain ⟨T, hT⟩ := Finite.exists_le (fun i : Option (Fin m) =>
    ‖quadricCoordinate C.centre i‖ /
      (quadricCoordinate x i * conj (quadricCoordinate C.centre i)).re)
  obtain ⟨K, hK⟩ := exists_rat_gt (max (1:ℝ) T)
  refine ⟨K, (le_max_left _ _).trans_lt hK, ?_⟩
  intro i hi
  exact (div_lt_iff₀ (C.source_positive hx hi)).mp ((hT i).trans_lt ((le_max_right _ _).trans_lt hK))

/-- Every genuine geometric overlap admits a scalar certificate. The choices here are
only in this existence proof; decoding and searching use finite rational data. -/
theorem exists_overlapCode (C E : QuadricRootChart a) (B A : RawCoordinateBox (locus a))
    (hB : B.chart = C.chart) (hA : A.chart = E.chart)
    (hBA : (B.carrier ∩ A.carrier).Nonempty) :
    ∃ code : OverlapCode, OverlapValid C E B A code := by
  obtain ⟨x, hxB, hxA⟩ := hBA
  have hxC : x ∈ C.chart.source := hB ▸ hxB.1
  have hxE : x ∈ E.chart.source := hA ▸ hxA.1
  let u := C.chart x
  have hu : u ∈ C.chart.target := C.chart.map_source hxC
  have hux : C.chart.symm u = x := C.chart.left_inv hxC
  have hY : ContinuousAt C.chart.symm u := C.chart.continuousAt_symm hu
  have hQ (i : Option (Fin m)) : ContinuousAt
      (fun q : Plane => quadricCoordinate (C.chart.symm q) i) u :=
    (quadricCoordinate_continuous i).continuousAt.comp hY
  obtain ⟨K, hK, hKB⟩ := C.exists_secant_bound hxC
  have htarget : ∀ᶠ q in 𝓝 u, q ∈ C.chart.target := C.chart.open_target.mem_nhds hu
  have hinside : ∀ᶠ q in 𝓝 u, dist q B.point < B.radius :=
    (continuousAt_id.dist continuousAt_const).eventually_lt continuousAt_const (by
      simpa only [u, ← hB, id_eq, Set.mem_preimage, Metric.mem_ball] using hxB.2)
  have hsecants : ∀ᶠ q in 𝓝 u, ∀ i, i ≠ C.tag → ‖quadricCoordinate C.centre i‖ <
      (K:ℝ) * (quadricCoordinate (C.chart.symm q) i * conj (quadricCoordinate C.centre i)).re := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i = C.tag
    · exact Filter.Eventually.of_forall fun _ hn => (hn hi).elim
    · have hh : ∀ᶠ q in 𝓝 u, ‖quadricCoordinate C.centre i‖ <
          (K:ℝ) * (quadricCoordinate (C.chart.symm q) i * conj (quadricCoordinate C.centre i)).re :=
        continuousAt_const.eventually_lt (continuousAt_const.mul (Complex.continuous_re.continuousAt.comp ((hQ i).mul continuousAt_const)))
          (by simpa only [hux] using hKB i hi)
      exact hh.mono fun q hq _ => hq
  have hsigns : ∀ᶠ q in 𝓝 u, ∀ i, i ≠ E.tag →
      0 < (quadricCoordinate (C.chart.symm q) i * conj (quadricCoordinate E.centre i)).re := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i = E.tag
    · exact Filter.Eventually.of_forall fun _ hn => (hn hi).elim
    · have hh : ∀ᶠ q in 𝓝 u, 0 <
          (quadricCoordinate (C.chart.symm q) i * conj (quadricCoordinate E.centre i)).re :=
        continuousAt_const.eventually_lt (Complex.continuous_re.continuousAt.comp ((hQ i).mul continuousAt_const))
          (by simpa only [hux] using E.source_positive hxE hi)
      exact hh.mono fun q hq _ => hq
  have hcoordinate : ∀ᶠ q in 𝓝 u, dist (E.chart (C.chart.symm q)) A.point < A.radius :=
    ((E.chart_continuous.continuousAt.comp hY).dist continuousAt_const).eventually_lt
      continuousAt_const (by simpa only [Function.comp_def, hux, ← hA, Set.mem_preimage, Metric.mem_ball] using hxA.2)
  have hnear : {q : Plane | q ∈ C.chart.target ∧ dist q B.point < B.radius ∧
      (∀ i, i ≠ C.tag → ‖quadricCoordinate C.centre i‖ <
        (K:ℝ) * (quadricCoordinate (C.chart.symm q) i * conj (quadricCoordinate C.centre i)).re) ∧
      (∀ i, i ≠ E.tag → 0 <
        (quadricCoordinate (C.chart.symm q) i * conj (quadricCoordinate E.centre i)).re) ∧
      dist (E.chart (C.chart.symm q)) A.point < A.radius} ∈ 𝓝 u := by
    filter_upwards [htarget, hinside, hsecants, hsigns, hcoordinate] with q h₁ h₂ h₃ h₄ h₅
    exact ⟨h₁,h₂,h₃,h₄,h₅⟩
  obtain ⟨q, hq⟩ := rationalPlane_dense.mem_nhds hnear
  let L : ℝ := variationFactor q K
  have hrinside : ∀ᶠ r : ℝ in 𝓝 0, dist (rationalPlane q) B.point + r < B.radius :=
    (continuousAt_const.add continuousAt_id).eventually_lt continuousAt_const (by simpa using hq.2.1)
  have hrsigns : ∀ᶠ r : ℝ in 𝓝 0, ∀ i, i ≠ E.tag → 2*r*L*‖quadricCoordinate E.centre i‖ <
      (quadricCoordinate (C.chart.symm (rationalPlane q)) i * conj (quadricCoordinate E.centre i)).re := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : i = E.tag
    · exact Filter.Eventually.of_forall fun _ hn => (hn hi).elim
    · have hh : ∀ᶠ r : ℝ in 𝓝 0, 2*r*L*‖quadricCoordinate E.centre i‖ <
          (quadricCoordinate (C.chart.symm (rationalPlane q)) i * conj (quadricCoordinate E.centre i)).re :=
        (((continuousAt_const.mul continuousAt_id).mul continuousAt_const).mul continuousAt_const).eventually_lt
          continuousAt_const (by simpa using hq.2.2.2.1 i hi)
      exact hh.mono fun r hr _ => hr
  have hrcoordinate : ∀ᶠ r : ℝ in 𝓝 0, dist (E.chart (C.chart.symm (rationalPlane q))) A.point + 2*r*L < A.radius :=
    (continuousAt_const.add ((continuousAt_const.mul continuousAt_id).mul continuousAt_const)).eventually_lt
      continuousAt_const (by simpa using hq.2.2.2.2)
  have hrsmall : ∀ᶠ r : ℝ in 𝓝 0, r < 1 := isOpen_Iio.mem_nhds (by norm_num)
  have hrnear : {r : ℝ | r < 1 ∧ dist (rationalPlane q) B.point + r < B.radius ∧
      (∀ i, i ≠ E.tag → 2*r*L*‖quadricCoordinate E.centre i‖ <
        (quadricCoordinate (C.chart.symm (rationalPlane q)) i * conj (quadricCoordinate E.centre i)).re) ∧
      dist (E.chart (C.chart.symm (rationalPlane q))) A.point + 2*r*L < A.radius} ∈ 𝓝 0 := by
    filter_upwards [hrsmall, hrinside, hrsigns, hrcoordinate] with r h₁ h₂ h₃ h₄
    exact ⟨h₁,h₂,h₃,h₄⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hrnear
  obtain ⟨r, hr, hrδ⟩ := exists_rat_btwn hδ
  have hradius := hball (show (r:ℝ) ∈ Metric.ball 0 δ by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_of_nonneg hr.le] using hrδ)
  exact ⟨⟨q,r,K⟩, hr, hradius.1, hK, hradius.2.1, hq.2.2.1, hradius.2.2.1, hradius.2.2.2⟩

/-- Every scalar certificate decodes to an overlap box in the child chart. -/
def overlapBox (C E : QuadricRootChart a) (B A : RawCoordinateBox (locus a))
    (hB : B.chart = C.chart) (code : OverlapCode) (h : OverlapValid C E B A code) :
    RawCoordinateBox (locus a) := C.offsetBox B hB code.point code.radius h.radius_pos h.inside

lemma overlapBox_subset (C E : QuadricRootChart a) (B A : RawCoordinateBox (locus a))
    (hB : B.chart = C.chart) (hA : A.chart = E.chart)
    (code : OverlapCode) (h : OverlapValid C E B A code) :
    (C.overlapBox E B A hB code h).compactCarrier ⊆ B.carrier ∩ A.carrier := by
  intro x hx
  refine ⟨C.offsetBox_compactCarrier_subset B hB code.point code.radius h.radius_pos h.inside hx, ?_⟩
  obtain ⟨z, hz, rfl⟩ := hx
  let y := C.chart.symm (rationalPlane code.point)
  have hzT : z ∈ C.chart.target := (C.offsetBox B hB code.point code.radius h.radius_pos h.inside).closed_subset hz
  have hqT : rationalPlane code.point ∈ C.chart.target :=
    (C.offsetBox B hB code.point code.radius h.radius_pos h.inside).closed_subset
      (Metric.mem_closedBall_self h.radius_pos.le)
  have hX : C.chart.symm z ∈ C.chart.source := C.chart.map_target hzT
  have hy : C.chart y = rationalPlane code.point := C.chart.right_inv hqT
  have hfree : quadricCoordinate (C.chart.symm z) C.tag ∈
      Metric.closedBall (quadricCoordinate y C.tag) (2*(code.radius:ℝ)) := by
    have hz' : z ∈ Metric.closedBall (rationalPlane code.point) (code.radius:ℝ) := hz
    have hh := realProd_closedBall_to_complex hz'
    have he₁ : quadricCoordinate (C.chart.symm z) C.tag = Complex.equivRealProdCLM.symm z := by
      apply Complex.equivRealProdCLM.injective
      rw [← C.chart_apply, C.chart.right_inv hzT, ContinuousLinearEquiv.apply_symm_apply]
    have he₂ : quadricCoordinate y C.tag = Complex.equivRealProdCLM.symm (rationalPlane code.point) := by
      apply Complex.equivRealProdCLM.injective
      rw [← C.chart_apply, hy, ContinuousLinearEquiv.apply_symm_apply]
    simpa only [he₁, he₂] using hh
  have hvar (i : Option (Fin m)) := C.coordinate_disc_bound hX code.point
    h.radius_pos h.radius_lt_one (by linarith [h.bound_gt_one]) hy hfree
    (fun i hi => (h.secants i hi).le) i
  have hdist : dist (E.chart (C.chart.symm z)) A.point < A.radius := by
    have hh := dist_triangle (E.chart (C.chart.symm z)) (E.chart y) A.point
    have hc := (E.chart_dist_le (C.chart.symm z) y).trans (hvar E.tag)
    linarith [h.coordinate]
  have htarget : E.chart (C.chart.symm z) ∈ E.chart.target := by
    rw [← hA]
    apply A.closed_subset
    change dist (A.chart (C.chart.symm z)) A.point ≤ A.radius
    rw [hA]
    exact hdist.le
  have hsource : C.chart.symm z ∈ E.chart.source := by
    apply E.source_of_target_positive htarget
    intro i hi
    exact halfplane_positive_of_close (hvar i) (h.signs i hi)
  exact ⟨hA.symm ▸ hsource, hA.symm ▸ hdist⟩

end QuadricRootChart
/-- Finite sign vectors in a fixed recursive order; no arbitrary enumeration of a Fintype. -/
def quadricSignVectors : (m : ℕ) → List (Fin m → Bool)
  | 0 => [fun i => Fin.elim0 i]
  | m+1 => (quadricSignVectors m).flatMap fun f => [Fin.cons false f, Fin.cons true f]

lemma mem_quadricSignVectors (m : ℕ) (f : Fin m → Bool) : f ∈ quadricSignVectors m := by
  induction m with
  | zero =>
      have he : f = fun i => Fin.elim0 i := funext fun i => Fin.elim0 i
      simp [quadricSignVectors, he]
  | succ m ih =>
      apply List.mem_flatMap.mpr
      refine ⟨Fin.tail f, ih _, ?_⟩
      have he := Fin.cons_self_tail f
      cases hf : f 0
      · exact List.mem_cons.mpr (Or.inl (by simpa only [hf] using he.symm))
      · exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr (by simpa only [hf] using he.symm)))

def finiteSubtypeList {I : Type} (p : I → Prop) [DecidablePred p] (l : List I) : List {i // p i} :=
  l.filterMap fun i => if hi : p i then some ⟨i,hi⟩ else none

lemma mem_finiteSubtypeList {I : Type} (p : I → Prop) [DecidablePred p] {l : List I}
    (i : {i // p i}) (hi : i.val ∈ l) : i ∈ finiteSubtypeList p l := by
  apply List.mem_filterMap.mpr
  exact ⟨i.val,hi,by simp only [dif_pos i.property]⟩

def quadricOrdinaryVertices {m : ℕ} (a : Fin m → ℚ) (R : ℚ) :
    List (OrdinaryGridIndex a R (quadricGridRadius R) quadricGridThreshold
      (quadricGridSize R) (quadricGridMesh R)) :=
  (finiteSubtypeList (fun i : Fin (2*quadricGridSize R+1) × Fin (2*quadricGridSize R+1) =>
      rationalOrdinaryValid a R (quadricGridRadius R) quadricGridThreshold
        (rationalGridPoint (quadricGridSize R) (quadricGridMesh R) i))
    ((List.finRange (2*quadricGridSize R+1)).product (List.finRange (2*quadricGridSize R+1)))).product
      (quadricSignVectors m)

def quadricTightOrdinaryVertices {m : ℕ} (a : Fin m → ℚ) (R : ℚ) :
    List (QuadricTightOrdinaryIndex a R) :=
  finiteSubtypeList (fun i : OrdinaryGridIndex a R (quadricGridRadius R) quadricGridThreshold
      (quadricGridSize R) (quadricGridMesh R) =>
    rationalNormSq (rationalGridPoint (quadricGridSize R) (quadricGridMesh R) i.1.val) <
      (R+quadricGridRadius R/16)^2) (quadricOrdinaryVertices a R)

def quadricTightVertices {m : ℕ} (a : Fin m → ℚ) (R : ℚ) :
    List (QuadricTightFiniteIndex a R) :=
  (quadricTightOrdinaryVertices a R).map Sum.inl ++
    ((List.finRange m).product ([false,true].product (quadricSignVectors m))).map Sum.inr

lemma mem_quadricTightOrdinaryVertices {m : ℕ} (a : Fin m → ℚ) (R : ℚ)
    (idx : QuadricTightOrdinaryIndex a R) : idx ∈ quadricTightOrdinaryVertices a R := by
  apply mem_finiteSubtypeList
  apply List.mem_product.mpr
  refine ⟨?_, mem_quadricSignVectors m idx.val.2⟩
  apply mem_finiteSubtypeList
  exact List.mem_product.mpr ⟨by simp, by simp⟩

lemma mem_quadricTightVertices {m : ℕ} (a : Fin m → ℚ) (R : ℚ)
    (idx : QuadricTightFiniteIndex a R) : idx ∈ quadricTightVertices a R := by
  cases idx with
  | inl i =>
      exact List.mem_append_left _ (List.mem_map.mpr ⟨i,mem_quadricTightOrdinaryVertices a R i,rfl⟩)
  | inr i =>
      rcases i with ⟨j,ε₀,ε⟩
      apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨(j,ε₀,ε), ?_, rfl⟩
      apply List.mem_product.mpr
      refine ⟨by simp, List.mem_product.mpr ⟨?_,mem_quadricSignVectors m ε⟩⟩
      cases ε₀ <;> simp

def quadricZeroGrid (N : ℕ) : Fin (2*N+1) × Fin (2*N+1) :=
  (⟨N,by omega⟩,⟨N,by omega⟩)

lemma quadricZeroGrid_point (N : ℕ) (h : ℚ) :
    rationalGridPoint N h (quadricZeroGrid N) = (0,0) := by
  simp [quadricZeroGrid, rationalGridPoint, rationalGridCoordinate]

lemma rationalOrdinaryValid_zero {m : ℕ} (a : Fin m → ℚ) {R : ℚ} (hR : 0 ≤ R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) :
    rationalOrdinaryValid a R (quadricGridRadius R) quadricGridThreshold (0,0) := by
  refine ⟨quadricGridRadius_pos hR, (quadricGridRadius_bound hR).trans (by norm_num),
    by norm_num [quadricGridThreshold], quadricGrid_budget hR, ?_, ?_⟩
  · simp only [rationalNormSq, zero_pow (by decide : (2:ℕ) ≠ 0), add_zero]
    positivity
  · intro i
    have ha : (1:ℝ) ≤ |(a i:ℝ)| := by simpa using hsep₀ i
    have hs : (1:ℝ) ≤ (a i:ℝ)^2 := by nlinarith [sq_abs (a i:ℝ)]
    apply (Rat.cast_lt (K := ℝ)).mp
    norm_num [rationalSquareDifferenceNormSq, quadricGridThreshold]
    nlinarith

def quadricTightRoot {m : ℕ} (a : Fin m → ℚ) {R : ℚ} (hR : 0 ≤ R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) : QuadricTightFiniteIndex a R :=
  .inl ⟨(⟨quadricZeroGrid (quadricGridSize R), by
      rw [quadricZeroGrid_point]
      exact rationalOrdinaryValid_zero a hR hsep₀⟩,fun _ => false), by
    rw [quadricZeroGrid_point]
    simp only [rationalNormSq, zero_pow (by decide : (2:ℕ) ≠ 0), add_zero]
    have hr := quadricGridRadius_pos hR
    positivity⟩

#check_explicit quadricSignVectors
#check_explicit quadricTightVertices
#check_explicit quadricTightRoot

section TightAtlas
variable {m : ℕ} (a : Fin m → ℚ)
  [Fact (Injective (fun j => (a j:ℂ)))] [Fact (∀ j, (a j:ℂ) ≠ 0)]

def quadricTightRootChart {R : ℚ} (hR : 0 ≤ R)
    (idx : QuadricTightFiniteIndex a R) : QuadricRootChart (fun j => (a j:ℂ)) :=
  match idx with
  | .inl i =>
      let q := rationalGridPoint (quadricGridSize R) (quadricGridMesh R) i.val.1.val
      let hv := (rationalOrdinaryValid_sound a hR q i.val.1.property i.val.2).1
      ⟨ordinaryPresentationCenter (fun j => (a j:ℂ)) i.val.2 (rationalComplex q), none,
        QuadricBoxCode.ordinary_margin_regular _ hv.1 hv.2⟩
  | .inr (i, ε₀, ε) =>
      ⟨branchPresentationCenter (fun j => (a j:ℂ)) i ε₀ ε, some i,
        branchPresentationCenter_regular _ Fact.out Fact.out i ε₀ ε⟩

def quadricTightRationalPoint {R : ℚ} (idx : QuadricTightFiniteIndex a R) : ℚ × ℚ :=
  match idx with
  | .inl i => rationalGridPoint (quadricGridSize R) (quadricGridMesh R) i.val.1.val
  | .inr _ => (0, 0)

def quadricTightRationalRadius {R : ℚ} (idx : QuadricTightFiniteIndex a R) : ℚ :=
  match idx with
  | .inl _ => quadricGridRadius R
  | .inr _ => 1/8

lemma quadricTightRootChart_chart {R : ℚ} (hR : 0 ≤ R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j ≠ i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (idx : QuadricTightFiniteIndex a R) :
    (quadricTightFiniteBox a hR hsep₀ hsep idx).chart = (quadricTightRootChart a hR idx).chart := by
  cases idx with
  | inl i => rfl
  | inr i => rcases i with ⟨i, ε₀, ε⟩; rfl

lemma quadricTightFiniteBox_point {R : ℚ} (hR : 0 ≤ R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j ≠ i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (idx : QuadricTightFiniteIndex a R) :
    (quadricTightFiniteBox a hR hsep₀ hsep idx).point =
      rationalPlane (quadricTightRationalPoint a idx) := by
  cases idx with
  | inl i => rfl
  | inr i =>
      rcases i with ⟨i, ε₀, ε⟩
      simp [quadricTightFiniteBox, uniformBranchBox, branchRawBox, branchPresentationCenter,
        quadricTightRationalPoint, rationalPlane]

lemma quadricTightFiniteBox_radius {R : ℚ} (hR : 0 ≤ R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j ≠ i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (idx : QuadricTightFiniteIndex a R) :
    (quadricTightFiniteBox a hR hsep₀ hsep idx).radius =
      (quadricTightRationalRadius a idx : ℝ) := by
  cases idx with
  | inl i => rfl
  | inr i => rcases i with ⟨i, ε₀, ε⟩; norm_num [quadricTightRationalRadius, quadricTightFiniteBox, uniformBranchBox, branchRawBox]

lemma QuadricRootChart.inverse_coordinate {m : ℕ} {a : Fin m → ℂ}
    (C : QuadricRootChart a) (q : ℚ × ℚ) (k : Option (Fin m)) :
    quadricCoordinate (C.chart.symm (rationalPlane q)) k =
      if k = C.tag then rationalComplex q else
        rootNear (quadricCoordinate C.centre k)
          ((rationalComplex q)^2-(quadricCoordinate C.centre C.tag)^2) := by
  rcases C with ⟨c, tag, hc⟩
  cases tag with
  | none =>
      cases k with
      | none => rfl
      | some j => rfl
  | some i =>
      cases k with
      | none => rfl
      | some j =>
          by_cases hj : j=i
          · subst j
            change (if i=i then rationalComplex q else _) = (if some i=some i then _ else _)
            simp
          · change (if j=i then rationalComplex q else _) = (if some j=some i then _ else _)
            simp only [hj, Option.some.injEq, if_false]
            rfl

/- Algebraic centres and inverse coordinates have uniform finite digit evaluators.
The original rational data determine every complex square-root branch. -/
open SymplecticPacking.Effective
open SymplecticPacking.Effective.AlgebraicComplex

private def gauss (O : Set (ℕ →. ℕ)) (q : ℚ × ℚ) : GaussianFamily O :=
  GaussianFamily.constant q.1 q.2

private lemma gauss_eval (O : Set (ℕ →. ℕ)) (q : ℚ × ℚ) (c : ℕ) :
    (gauss O q).eval c = rationalComplex q := by
  rw [gauss, GaussianFamily.constant_at]
  apply Complex.ext <;> simp [rationalComplex, Complex.equivRealProdCLM_symm_apply]

@[simp] private lemma rationalComplex_real (x : ℚ) : rationalComplex (x,0) = (x:ℂ) := by
  simp [rationalComplex, Complex.equivRealProdCLM_symm_apply]

/-- Four raw rational codes, decoded without rational normalization. -/
def QuadricRootChart.OverlapCode.decode (c : ℕ) : QuadricRootChart.OverlapCode where
  point := (RationalCode.value (Nat.unpair (Nat.unpair c).1).1,
    RationalCode.value (Nat.unpair (Nat.unpair c).1).2)
  radius := RationalCode.value (Nat.unpair (Nat.unpair c).2).1
  bound := RationalCode.value (Nat.unpair (Nat.unpair c).2).2

lemma QuadricRootChart.OverlapCode.decode_surjective : Surjective QuadricRootChart.OverlapCode.decode := by
  intro code
  refine ⟨Nat.pair (Nat.pair (RationalCode.ofRat code.point.1) (RationalCode.ofRat code.point.2))
    (Nat.pair (RationalCode.ofRat code.radius) (RationalCode.ofRat code.bound)), ?_⟩
  cases code
  simp [QuadricRootChart.OverlapCode.decode, RationalCode.value_ofRat]

private def candidatePoint (O : Set (ℕ →. ℕ)) : GaussianFamily O :=
  ⟨fun c => (Nat.unpair (Nat.unpair c).1).1, fun c => (Nat.unpair (Nat.unpair c).1).2,
    Oracle.of_computable (Primrec.fst.comp (Primrec.unpair.comp
      (Primrec.fst.comp Primrec.unpair))).to_comp,
    Oracle.of_computable (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.fst.comp Primrec.unpair))).to_comp⟩

private lemma candidatePoint_eval (O : Set (ℕ →. ℕ)) (c : ℕ) :
    (candidatePoint O).eval c = rationalComplex (QuadricRootChart.OverlapCode.decode c).point := by
  apply Complex.ext <;> simp [candidatePoint, GaussianFamily.eval, AlgebraicComplex.value,
    QuadricRootChart.OverlapCode.decode, rationalComplex, Complex.equivRealProdCLM_symm_apply]

private def candidateRadius (O : Set (ℕ →. ℕ)) :
    Family.Evaluator O (fun c => ((QuadricRootChart.OverlapCode.decode c).radius:ℝ)) :=
  Family.Evaluator.rational (fun c => (Nat.unpair (Nat.unpair c).2).1)
    (Oracle.of_computable (Primrec.fst.comp (Primrec.unpair.comp
      (Primrec.snd.comp Primrec.unpair))).to_comp)

private def candidateBound (O : Set (ℕ →. ℕ)) :
    Family.Evaluator O (fun c => ((QuadricRootChart.OverlapCode.decode c).bound:ℝ)) :=
  Family.Evaluator.rational (fun c => (Nat.unpair (Nat.unpair c).2).2)
    (Oracle.of_computable (Primrec.snd.comp (Primrec.unpair.comp
      (Primrec.snd.comp Primrec.unpair))).to_comp)

private def rationalEvaluator (O : Set (ℕ →. ℕ)) (v : ℚ) :
    Family.Evaluator O (fun _ => (v:ℝ)) :=
  (Family.Evaluator.rational (fun _ => RationalCode.ofRat v)
    (Oracle.of_computable (Computable.const _))).congr (fun _ => by simp [RationalCode.value_ofRat])

private def candidateVariation (O : Set (ℕ →. ℕ)) :
    Family.Evaluator O (fun c => (QuadricRootChart.variationFactor
      (QuadricRootChart.OverlapCode.decode c).point (QuadricRootChart.OverlapCode.decode c).bound:ℝ)) := by
  let Q := (candidatePoint O).evaluator
  let one := rationalEvaluator O 1
  let two := rationalEvaluator O 2
  exact (one.add ((candidateBound O).mul
    ((two.mul (Q.re.absolute.add Q.im.absolute)).add two))).congr (fun c => by
      simp [QuadricRootChart.variationFactor, QuadricRootChart.OverlapCode.decode,
        candidatePoint, GaussianFamily.eval, AlgebraicComplex.value])

/-- Squared centre coordinates are Gaussian rational even when the centre is not. -/
def quadricTightCentreSquare (O : Set (ℕ →. ℕ)) {R : ℚ}
    (idx : QuadricTightFiniteIndex a R) (k : Option (Fin m)) : GaussianFamily O :=
  match idx, k with
  | .inl i, none =>
      let U := gauss O (quadricTightRationalPoint a (.inl i))
      U.mul U
  | .inl i, some j =>
      let U := gauss O (quadricTightRationalPoint a (.inl i))
      (U.mul U).add (gauss O (a j,0)).neg
  | .inr (i, _, _), none => gauss O (a i,0)
  | .inr (i, _, _), some j => gauss O (a i-a j,0)

lemma quadricTightCentreSquare_eval (O : Set (ℕ →. ℕ)) {R : ℚ} (hR : 0 ≤ R)
    (idx : QuadricTightFiniteIndex a R) (k : Option (Fin m)) (c : ℕ) :
    (quadricTightCentreSquare a O idx k).eval c =
      quadricCoordinate (quadricTightRootChart a hR idx).centre k ^ 2 := by
  cases idx with
  | inl i =>
      cases k with
      | none => simp [quadricTightCentreSquare, GaussianFamily.mul_at, gauss_eval,
          quadricTightRootChart, quadricCoordinate, ordinaryPresentationCenter,
          quadricTightRationalPoint, pow_two]
      | some j =>
          simp [quadricTightCentreSquare, GaussianFamily.mul_at, GaussianFamily.add_at,
            GaussianFamily.neg_at, gauss_eval, quadricTightRootChart, quadricCoordinate,
            ordinaryPresentationCenter, signedRoot_sq, quadricTightRationalPoint,
            rationalComplex_real, sub_eq_add_neg] <;> ring
  | inr i =>
      rcases i with ⟨i, ε₀, ε⟩
      cases k with
      | none => simp [quadricTightCentreSquare, gauss_eval, quadricTightRootChart,
          quadricCoordinate, branchPresentationCenter, signedRoot_sq, rationalComplex_real]
      | some j =>
          by_cases hj : j=i
          · subst j
            simp [quadricTightCentreSquare, gauss_eval, quadricTightRootChart,
              quadricCoordinate, branchPresentationCenter, rationalComplex_real]
          · simp [quadricTightCentreSquare, gauss_eval, quadricTightRootChart,
              quadricCoordinate, branchPresentationCenter, hj, signedRoot_sq, rationalComplex_real]

private def signedEvaluator {O : Set (ℕ →. ℕ)} {z : ℕ → ℂ}
    (Z : AlgebraicComplex.Evaluator O z) (ε : Bool) :
    AlgebraicComplex.Evaluator O (fun c => if ε then -z c else z c) := by
  cases ε
  · exact Z
  · exact Z.neg

def quadricTightCentreEvaluator (O : Set (ℕ →. ℕ)) {R : ℚ} (hR : 0 ≤ R)
    (idx : QuadricTightFiniteIndex a R) (k : Option (Fin m)) :
    AlgebraicComplex.Evaluator O (fun _ => quadricCoordinate (quadricTightRootChart a hR idx).centre k) := by
  cases idx with
  | inl i =>
      let U := gauss O (quadricTightRationalPoint a (.inl i))
      cases k with
      | none =>
          exact U.evaluator.congr (fun c => by
            simp [U, gauss_eval, quadricTightRootChart, quadricCoordinate,
              ordinaryPresentationCenter, quadricTightRationalPoint])
      | some j =>
          let S := (U.mul U).add (gauss O (a j,0)).neg
          exact (signedEvaluator S.root (i.val.2 j)).congr (fun c => by
            simp [S, U, GaussianFamily.add_at, GaussianFamily.mul_at, GaussianFamily.neg_at,
              gauss_eval, quadricTightRootChart, quadricCoordinate, ordinaryPresentationCenter,
              quadricTightRationalPoint, signedRoot, rationalComplex_real, pow_two, sub_eq_add_neg])
  | inr i =>
      rcases i with ⟨i, ε₀, ε⟩
      cases k with
      | none =>
          exact (signedEvaluator (gauss O (a i,0)).root ε₀).congr (fun c => by
            simp [gauss_eval, quadricTightRootChart, quadricCoordinate,
              branchPresentationCenter, signedRoot, rationalComplex_real])
      | some j =>
          by_cases hj : j=i
          · exact (gauss O (0,0)).evaluator.congr (fun c => by
              simp [gauss_eval, quadricTightRootChart, quadricCoordinate,
                branchPresentationCenter, hj, rationalComplex_real])
          · exact (signedEvaluator (gauss O (a i-a j,0)).root (ε j)).congr (fun c => by
              simp [gauss_eval, quadricTightRootChart, quadricCoordinate,
                branchPresentationCenter, hj, signedRoot, rationalComplex_real])

/-- All inverse-chart coordinates are evaluated by rational radicands. Squared centre
coordinates are used directly; no reciprocal of an arbitrary real name is required. -/
def quadricTightInverseEvaluator (O : Set (ℕ →. ℕ)) {R : ℚ} (hR : 0 ≤ R)
    (idx : QuadricTightFiniteIndex a R) (point : ℕ → ℚ × ℚ)
    (Q : GaussianFamily O) (hQ : ∀ c, Q.eval c = rationalComplex (point c))
    (k : Option (Fin m)) :
    AlgebraicComplex.Evaluator O (fun c =>
      quadricCoordinate ((quadricTightRootChart a hR idx).chart.symm (rationalPlane (point c))) k) := by
  let C := quadricTightRootChart a hR idx
  by_cases hk : k=C.tag
  · exact Q.evaluator.congr (fun c => by rw [C.inverse_coordinate, if_pos hk, hQ])
  · let S := quadricTightCentreSquare a O idx k
    let T := quadricTightCentreSquare a O idx C.tag
    let D := (Q.mul Q).add T.neg
    let A := (gauss O (1,0)).add (D.mul S.inverse)
    exact ((quadricTightCentreEvaluator a O hR idx k).mul A.root).congr (fun c => by
      rw [C.inverse_coordinate, if_neg hk]
      simp only [A, D, S, T, GaussianFamily.add_at, GaussianFamily.mul_at,
        GaussianFamily.neg_at, GaussianFamily.inverse_at, gauss_eval, rationalComplex_real,
        hQ, rootNear, div_eq_mul_inv]
      rw [quadricTightCentreSquare_eval a O hR idx C.tag c,
        quadricTightCentreSquare_eval a O hR idx k c]
      simp [C, pow_two, sub_eq_add_neg])

private def candidateDiscError (O : Set (ℕ →. ℕ)) :
    Family.Evaluator O (fun c => 2*((QuadricRootChart.OverlapCode.decode c).radius:ℝ)*
      (QuadricRootChart.variationFactor (QuadricRootChart.OverlapCode.decode c).point
        (QuadricRootChart.OverlapCode.decode c).bound:ℝ)) :=
  (((rationalEvaluator O 2).mul (candidateRadius O)).mul (candidateVariation O)).congr
    (fun _ => by norm_num)

private def pointDistanceEvaluator (O : Set (ℕ →. ℕ)) (p : ℚ × ℚ) :
    Family.Evaluator O (fun c => dist (rationalPlane (QuadricRootChart.OverlapCode.decode c).point)
      (rationalPlane p)) :=
  ((candidatePoint O).evaluator.planeDistance (gauss O p).evaluator).congr (fun c => by
    rw [candidatePoint_eval, gauss_eval]
    rfl)

private def inverseDistanceEvaluator (O : Set (ℕ →. ℕ)) {R : ℚ} (hR : 0 ≤ R)
    (idx jdx : QuadricTightFiniteIndex a R) :
    Family.Evaluator O (fun c => dist
      ((quadricTightRootChart a hR jdx).chart ((quadricTightRootChart a hR idx).chart.symm
        (rationalPlane (QuadricRootChart.OverlapCode.decode c).point)))
      (rationalPlane (quadricTightRationalPoint a jdx))) := by
  let Y := quadricTightInverseEvaluator a O hR idx
    (fun c => (QuadricRootChart.OverlapCode.decode c).point) (candidatePoint O) (candidatePoint_eval O)
    (quadricTightRootChart a hR jdx).tag
  exact (Y.planeDistance (gauss O (quadricTightRationalPoint a jdx)).evaluator).congr (fun c => by
    rw [gauss_eval, QuadricRootChart.chart_apply]
    rfl)

private def secantEvaluator (O : Set (ℕ →. ℕ)) {R : ℚ} (hR : 0 ≤ R)
    (idx : QuadricTightFiniteIndex a R) (k : Option (Fin m)) : Family.Margin O := by
  let C := quadricTightRootChart a hR idx
  if hk : k=C.tag then
    exact ⟨_,rationalEvaluator O 1⟩
  else
    let Z := quadricTightCentreEvaluator a O hR idx k
    let Y := quadricTightInverseEvaluator a O hR idx
      (fun c => (QuadricRootChart.OverlapCode.decode c).point) (candidatePoint O) (candidatePoint_eval O) k
    exact ⟨_,((candidateBound O).mul (Y.mul Z.conjugate).re).add Z.norm.neg⟩

private def signEvaluator (O : Set (ℕ →. ℕ)) {R : ℚ} (hR : 0 ≤ R)
    (idx jdx : QuadricTightFiniteIndex a R) (k : Option (Fin m)) : Family.Margin O := by
  let E := quadricTightRootChart a hR jdx
  if hk : k=E.tag then
    exact ⟨_,rationalEvaluator O 1⟩
  else
    let Z := quadricTightCentreEvaluator a O hR jdx k
    let Y := quadricTightInverseEvaluator a O hR idx
      (fun c => (QuadricRootChart.OverlapCode.decode c).point) (candidatePoint O) (candidatePoint_eval O) k
    exact ⟨_,(Y.mul Z.conjugate).re.add ((candidateDiscError O).mul Z.norm).neg⟩

private def allQuadricCoordinates (m : ℕ) : List (Option (Fin m)) :=
  none :: (List.finRange m).map some

private lemma mem_allQuadricCoordinates (k : Option (Fin m)) : k ∈ allQuadricCoordinates m := by
  cases k <;> simp [allQuadricCoordinates]

/-- These are exactly the scalar margins in `OverlapValid`, with the two redundant
free-coordinate tests set to 1. This list is the input to the finite checker. -/
def quadricOverlapMargins (O : Set (ℕ →. ℕ)) {R : ℚ} (hR : 0 ≤ R)
    (idx jdx : QuadricTightFiniteIndex a R) : List (Family.Margin O) :=
  [⟨_,candidateRadius O⟩,
   ⟨_,(rationalEvaluator O 1).add (candidateRadius O).neg⟩,
   ⟨_,(candidateBound O).add (rationalEvaluator O (-1))⟩,
   ⟨_,(rationalEvaluator O (quadricTightRationalRadius a idx)).add
     ((pointDistanceEvaluator O (quadricTightRationalPoint a idx)).add (candidateRadius O)).neg⟩] ++
  (allQuadricCoordinates m).map (secantEvaluator a O hR idx) ++
  (allQuadricCoordinates m).map (signEvaluator a O hR idx jdx) ++
  [⟨_,(rationalEvaluator O (quadricTightRationalRadius a jdx)).add
    ((inverseDistanceEvaluator a O hR idx jdx).add (candidateDiscError O)).neg⟩]

lemma quadricOverlapMargins_pos_iff (O : Set (ℕ →. ℕ)) {R : ℚ} (hR : 0 ≤ R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j ≠ i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (idx jdx : QuadricTightFiniteIndex a R) (c : ℕ) :
    (∀ M ∈ quadricOverlapMargins a O hR idx jdx, 0 < M.value c) ↔
      QuadricRootChart.OverlapValid (quadricTightRootChart a hR idx)
        (quadricTightRootChart a hR jdx) (quadricTightFiniteBox a hR hsep₀ hsep idx)
        (quadricTightFiniteBox a hR hsep₀ hsep jdx) (QuadricRootChart.OverlapCode.decode c) := by
  let C := quadricTightRootChart a hR idx
  let E := quadricTightRootChart a hR jdx
  let code := QuadricRootChart.OverlapCode.decode c
  have hsec (k : Option (Fin m)) :
      0 < (secantEvaluator a O hR idx k).value c ↔
        (k ≠ C.tag → ‖quadricCoordinate C.centre k‖ <
          (code.bound:ℝ)*(quadricCoordinate (C.chart.symm (rationalPlane code.point)) k *
            conj (quadricCoordinate C.centre k)).re) := by
    by_cases hk : k=C.tag
    · simp [secantEvaluator, C, hk]
    · have hk' : k ≠ (quadricTightRootChart a hR idx).tag := hk
      simp only [secantEvaluator, dif_neg hk']
      change ((0:ℝ) < _ + -_) ↔ (k ≠ C.tag → (_:ℝ) < _)
      constructor
      · intro hh _; linarith
      · intro hh; have hh' := hh hk; linarith
  have hsign (k : Option (Fin m)) :
      0 < (signEvaluator a O hR idx jdx k).value c ↔
        (k ≠ E.tag → 2*(code.radius:ℝ)*(QuadricRootChart.variationFactor code.point code.bound:ℝ)*
          ‖quadricCoordinate E.centre k‖ <
          (quadricCoordinate (C.chart.symm (rationalPlane code.point)) k *
            conj (quadricCoordinate E.centre k)).re) := by
    by_cases hk : k=E.tag
    · simp [signEvaluator, E, hk]
    · have hk' : k ≠ (quadricTightRootChart a hR jdx).tag := hk
      simp only [signEvaluator, dif_neg hk']
      change ((0:ℝ) < _ + -_) ↔ (k ≠ E.tag → (_:ℝ) < _)
      constructor
      · intro hh _; linarith
      · intro hh; have hh' := hh hk; linarith
  constructor
  · intro hm
    have hr := hm ⟨_,candidateRadius O⟩ (by simp [quadricOverlapMargins])
    have hr₁ := hm ⟨_,(rationalEvaluator O 1).add (candidateRadius O).neg⟩
      (by simp [quadricOverlapMargins])
    have hK := hm ⟨_,(candidateBound O).add (rationalEvaluator O (-1))⟩
      (by simp [quadricOverlapMargins])
    have hinside := hm ⟨_,(rationalEvaluator O (quadricTightRationalRadius a idx)).add
      ((pointDistanceEvaluator O (quadricTightRationalPoint a idx)).add (candidateRadius O)).neg⟩
      (by simp [quadricOverlapMargins])
    have hcoord := hm ⟨_,(rationalEvaluator O (quadricTightRationalRadius a jdx)).add
      ((inverseDistanceEvaluator a O hR idx jdx).add (candidateDiscError O)).neg⟩
      (by simp [quadricOverlapMargins])
    change 0 < (code.radius:ℝ) at hr
    change 0 < ((1:ℚ):ℝ) + -(code.radius:ℝ) at hr₁
    norm_num at hr₁
    change 0 < (code.bound:ℝ)+((-1:ℚ):ℝ) at hK
    norm_num at hK
    change 0 < (quadricTightRationalRadius a idx:ℝ) +
      -(dist (rationalPlane code.point) (rationalPlane (quadricTightRationalPoint a idx))+(code.radius:ℝ)) at hinside
    change 0 < (quadricTightRationalRadius a jdx:ℝ) +
      -(dist (E.chart (C.chart.symm (rationalPlane code.point)))
        (rationalPlane (quadricTightRationalPoint a jdx))+
        2*(code.radius:ℝ)*(QuadricRootChart.variationFactor code.point code.bound:ℝ)) at hcoord
    refine ⟨hr, by linarith, by linarith, ?_, ?_, ?_, ?_⟩
    · rw [quadricTightFiniteBox_point, quadricTightFiniteBox_radius]; linarith
    · intro k hk
      exact (hsec k).mp (hm _ (by
        simp only [quadricOverlapMargins, List.mem_append, List.mem_map]
        exact Or.inl (Or.inl (Or.inr ⟨k,mem_allQuadricCoordinates k,rfl⟩)))) hk
    · intro k hk
      exact (hsign k).mp (hm _ (by
        simp only [quadricOverlapMargins, List.mem_append, List.mem_map]
        exact Or.inl (Or.inr ⟨k,mem_allQuadricCoordinates k,rfl⟩))) hk
    · rw [quadricTightFiniteBox_point, quadricTightFiniteBox_radius]; linarith
  · intro hv
    have hi := hv.inside
    have hc := hv.coordinate
    rw [quadricTightFiniteBox_point, quadricTightFiniteBox_radius] at hi hc
    intro M hM
    simp only [quadricOverlapMargins, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map] at hM
    rcases hM with ((hM | hM) | hM) | hM
    · rcases hM with rfl | rfl | rfl | rfl
      · exact hv.radius_pos
      · change 0 < ((1:ℚ):ℝ)+-(code.radius:ℝ); norm_num; linarith [hv.radius_lt_one]
      · change 0 < (code.bound:ℝ)+((-1:ℚ):ℝ); norm_num; linarith [hv.bound_gt_one]
      · change 0 < (quadricTightRationalRadius a idx:ℝ)+
          -(dist (rationalPlane code.point) (rationalPlane (quadricTightRationalPoint a idx))+(code.radius:ℝ))
        linarith
    · rcases hM with ⟨k,_,rfl⟩
      exact (hsec k).mpr (fun hk => hv.secants k hk)
    · rcases hM with ⟨k,_,rfl⟩
      exact (hsign k).mpr (fun hk => hv.signs k hk)
    · subst M
      change 0 < (quadricTightRationalRadius a jdx:ℝ)+
        -(dist (E.chart (C.chart.symm (rationalPlane code.point)))
          (rationalPlane (quadricTightRationalPoint a jdx))+
          2*(code.radius:ℝ)*(QuadricRootChart.variationFactor code.point code.bound:ℝ))
      linarith

/-- The overlap checker makes finitely many rational digit queries and natural
comparisons. The candidate and precision are paired in its sole natural input. -/
def quadricOverlapCheck {R : ℚ} (hR : 0 ≤ R) (idx jdx : QuadricTightFiniteIndex a R) : ℕ → ℕ :=
  Family.Margin.check (quadricOverlapMargins a ∅ hR idx jdx)

lemma quadricOverlapCheck_sound {R : ℚ} (hR : 0 ≤ R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j ≠ i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (idx jdx : QuadricTightFiniteIndex a R) {s : ℕ}
    (hs : quadricOverlapCheck a hR idx jdx s=0) :
    QuadricRootChart.OverlapValid (quadricTightRootChart a hR idx)
      (quadricTightRootChart a hR jdx) (quadricTightFiniteBox a hR hsep₀ hsep idx)
      (quadricTightFiniteBox a hR hsep₀ hsep jdx)
      (QuadricRootChart.OverlapCode.decode (Nat.unpair s).1) := by
  apply (quadricOverlapMargins_pos_iff a ∅ hR hsep₀ hsep idx jdx _).mp
  exact (Family.Margin.row_pos_iff _ _).mp (Family.Margin.check_sound _ hs)

lemma exists_quadricOverlapCheck {R : ℚ} (hR : 0 ≤ R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j ≠ i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (idx jdx : QuadricTightFiniteIndex a R)
    (hij : ((quadricTightFiniteBox a hR hsep₀ hsep idx).carrier ∩
      (quadricTightFiniteBox a hR hsep₀ hsep jdx).carrier).Nonempty) :
    ∃ s, quadricOverlapCheck a hR idx jdx s=0 := by
  obtain ⟨code,hcode⟩ := QuadricRootChart.exists_overlapCode _ _ _ _
    (quadricTightRootChart_chart a hR hsep₀ hsep idx)
    (quadricTightRootChart_chart a hR hsep₀ hsep jdx) hij
  obtain ⟨c,rfl⟩ := QuadricRootChart.OverlapCode.decode_surjective code
  apply Family.Margin.exists_check
  refine ⟨c,(Family.Margin.row_pos_iff _ _).mpr ?_⟩
  exact (quadricOverlapMargins_pos_iff a ∅ hR hsep₀ hsep idx jdx c).mpr hcode

/-- A successful finite check directly decodes its certified compact overlap box. -/
def quadricCheckedOverlap {R : ℚ} (hR : 0 ≤ R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j ≠ i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (idx jdx : QuadricTightFiniteIndex a R) (s : ℕ)
    (hs : quadricOverlapCheck a hR idx jdx s=0) : RawCoordinateBox (locus (fun j => (a j:ℂ))) :=
  QuadricRootChart.overlapBox _ _ _ _ (quadricTightRootChart_chart a hR hsep₀ hsep idx)
    (QuadricRootChart.OverlapCode.decode (Nat.unpair s).1)
    (quadricOverlapCheck_sound a hR hsep₀ hsep idx jdx hs)

lemma quadricCheckedOverlap_chart {R : ℚ} (hR : 0 ≤ R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j ≠ i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (idx jdx : QuadricTightFiniteIndex a R) (s : ℕ)
    (hs : quadricOverlapCheck a hR idx jdx s=0) :
    (quadricCheckedOverlap a hR hsep₀ hsep idx jdx s hs).chart =
      (quadricTightRootChart a hR idx).chart := rfl

lemma quadricCheckedOverlap_subset {R : ℚ} (hR : 0 ≤ R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j ≠ i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (idx jdx : QuadricTightFiniteIndex a R) (s : ℕ)
    (hs : quadricOverlapCheck a hR idx jdx s=0) :
    (quadricCheckedOverlap a hR hsep₀ hsep idx jdx s hs).compactCarrier ⊆
      (quadricTightFiniteBox a hR hsep₀ hsep idx).carrier ∩
      (quadricTightFiniteBox a hR hsep₀ hsep jdx).carrier :=
  QuadricRootChart.overlapBox_subset _ _ _ _ (quadricTightRootChart_chart a hR hsep₀ hsep idx)
    (quadricTightRootChart_chart a hR hsep₀ hsep jdx) _
    (quadricOverlapCheck_sound a hR hsep₀ hsep idx jdx hs)

#check_explicit quadricOverlapCheck
#check_explicit quadricCheckedOverlap

#check_explicit quadricTightCentreEvaluator
#check_explicit quadricTightInverseEvaluator

end TightAtlas

end SymplecticPacking.HighDim.ToricPackingStages
