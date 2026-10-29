import SymplecticPacking.HighDim.Comparator.Poly
import SymplecticPacking.HighDim.Comparator.Isotopy
import SymplecticPacking.HighDim.Comparator.PlanarGen
import SymplecticPacking.HighDim.Comparator.PlanarGenSpecCore
import SymplecticPacking.HighDim.Comparator.PlanarGenEndpoint
import SymplecticPacking.HighDim.Comparator.PlanarInnerFamily
import SymplecticPacking.HighDim.Comparator.PlanarSliceBounds
import SymplecticPacking.HighDim.Comparator.PlanarCutoffBounds
import SymplecticPacking.HighDim.Comparator.PlanarJointInner
import SymplecticPacking.HighDim.Comparator.PlanarParamHamiltonian

/-!
# Building blocks of `realiseGen` (paper `thm:cmp-realisation`)

The generator `Q^{(j)}` realising one rearrangement `R_j` is the lift

  `Q(t, z) = χ(y) · S'(t) · ℓ(y) · B(y, χ(y) S(t), z_j / √ℓ(y))`,

where `y` are the other moments (`y_j` set to `0`), `S = Real.smoothTransition` is the flat
time step, `ℓ` is the smooth soft-min inner slice length, `χ` the explicit cutoff
(length factor × box factor), and `B` the *planar* generator of the uniform
parameterised planar rearrangement. Everything except `B` is a closed formula
here. The planar generator `planarGen` is the explicit five-segment construction;
`planarGen_ordinary`, `planarGen_smooth` and `planarGen_endpoint` establish its contract
`planarGen_spec`. Joint smoothness uses the open finite coefficient envelope containing
the closed parameter-cutoff support.

The factor `S'(t)` makes the generator vanish for `t ∉ [0, 1]` (the stage runs the planar
isotopy up to time `χ(y)`), and `ℓ(y)` is the area rescaling `w = z_j/√ℓ`.
-/

noncomputable section

namespace SymplecticPacking.HighDim.RealiseGen

open Set Filter Topology
open OAI.PackingSufficiencySupport.Hamiltonian (planeMoments)
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff

variable {m q : ℕ}

/-- The plane `ℝ²` (one factor of the fibre). -/
abbrev Plane := ℝ × ℝ

/-- Capacity of a planar point, `π|w|²`. -/
def planeArea (w : Plane) : ℝ := Real.pi * (w.1 ^ 2 + w.2 ^ 2)

/-! ### Explicit parameters -/

/-- Slope bound `L_p = 1 + Σ_r |∂_j ℓ_r|` of the pieces of `F` in direction `j`. -/
def slopeBound (F : PolyFn m) (j : Fin m) : ℝ := (F.map fun a => |a.coef j|).sum + 1

/-- `η₀ = e / (64 L_p)`. -/
def eta0 (F : PolyFn m) (j : Fin m) (e : ℝ) : ℝ := e / (64 * slopeBound F j)

/-- `ζ = η₀ / 8`. -/
def zeta (F : PolyFn m) (j : Fin m) (e : ℝ) : ℝ := eta0 F j e / 8

/-- Soft-min temperature `s₀ = ζ / (4(q+1))`. -/
def softTemp (q : ℕ) (F : PolyFn m) (j : Fin m) (e : ℝ) : ℝ := zeta F j e / (4 * (q + 1))

/-- Soft-min offset `δ₀ = ζ / 4`. -/
def softShift (F : PolyFn m) (j : Fin m) (e : ℝ) : ℝ := zeta F j e / 4

/-- Planar tolerance `ξ = e / 4`. -/
def planarTol (e : ℝ) : ℝ := e / 4

/-- Box radius `R = 2 + Σ_i Σ_{ν : b_{νi} > 0} ℓ_ν / b_{νi}`; the projection of `Δ` lies in
`‖y‖_∞ < R − 1`. -/
def boxRad (Δ : Polytope m q) : ℝ :=
  2 + ∑ i, ∑ ν, (if 0 < Δ.b ν i then Δ.ℓ ν / Δ.b ν i else 0)

/-- The affine slice bound of face `ν` in direction `j`:
`L_ν(y) = (ℓ_ν − Σ_{i≠j} b_{νi} y_i) / b_{νj}` (the summands of `Polytope.sliceLen`). -/
def faceLen (Δ : Polytope m q) (j : Fin m) (ν : Fin q) (y : Moments m) : ℝ :=
  (Δ.ℓ ν - ∑ i, (if i = j then 0 else Δ.b ν i * y i)) / Δ.b ν j

/-- Smooth soft minimum of the slice bounds:
`ℓ(y) = −s₀ log Σ_{ν : b_{νj}>0} exp(−L_ν(y)/s₀) − δ₀`. -/
def softLen (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) (y : Moments m) : ℝ :=
  -softTemp q F j e *
      Real.log (∑ ν, (if 0 < Δ.b ν j then
        Real.exp (-faceLen Δ j ν y / softTemp q F j e) else 0)) -
    softShift F j e

/-- Length cutoff `χ_L(y) = Π_{ν : b_{νj}>0} S((L_ν(y) − 5η₀/4)/(η₀/2))`. -/
def lenCut (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) (y : Moments m) : ℝ :=
  ∏ ν, (if 0 < Δ.b ν j then
    Real.smoothTransition ((faceLen Δ j ν y - 5 * eta0 F j e / 4) / (eta0 F j e / 2)) else 1)

/-- Box cutoff `ρ_box(y) = Π_{i≠j} (1 − S((y_i² − R²)/(3R²)))`. -/
def boxCut (Δ : Polytope m q) (j : Fin m) (y : Moments m) : ℝ :=
  ∏ i, (if i = j then 1 else
    1 - Real.smoothTransition ((y i ^ 2 - boxRad Δ ^ 2) / (3 * boxRad Δ ^ 2)))

/-- The parameter cutoff `χ = ρ_box · χ_L`. -/
def cut (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) (y : Moments m) : ℝ :=
  boxCut Δ j y * lenCut Δ F j e y

/-- The planar parameter compact `Y_big = {‖y‖_∞ ≤ 3R, all L_ν(y) ≥ 3η₀/4}` (with `y_j = 0`). -/
def bigParams (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) : Set (Moments m) :=
  {y | y j = 0 ∧ (∀ i, |y i| ≤ 3 * boxRad Δ) ∧
    ∀ ν, 0 < Δ.b ν j → 3 * eta0 F j e / 4 ≤ faceLen Δ j ν y}

/-- The normalised slice family `f_y(v) = F(y, ℓ(y) v)`, `0 ≤ v ≤ 1`. -/
def sliceFn (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) (y : Moments m) (v : ℝ) : ℝ :=
  PolyFn.eval F (Function.update y j (softLen Δ F j e y * v))

/-- The increasing rearrangement on `[0,1]`: `(R g)(x) = inf_{0 ≤ a ≤ 1−x} max(g a, g(a+x))`. -/
def unitRearr (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ⨅ a : Icc (0 : ℝ) (1 - x), max (g a) (g (a + x))

/-! ### The planar generator -/

/-- Hamiltonian field of a planar generator, convention `ι_X ω = −dB`. -/
def planarVF (B : Moments m → ℝ → Plane → ℝ) (y : Moments m) (s : ℝ) (w : Plane) : Plane :=
  (-(fderiv ℝ (B y s) w (0, 1)), fderiv ℝ (B y s) w (1, 0))

/-- Contract of the parameterised planar rearrangement. -/
structure PlanarSpec (f : Moments m → ℝ → ℝ) (Y : Set (Moments m)) (ξ : ℝ)
    (B : Moments m → ℝ → Plane → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ (fun x : Moments m × ℝ × Plane => B x.1 x.2.1 x.2.2)
  /-- common spatial support inside a disc of capacity `r_B < 1`. -/
  support : ∃ rB < 1, ∀ y s w, rB < planeArea w → B y s w = 0
  /-- the time-one map realises the rearrangement on `D(1)` up to `ξ`, uniformly on `Y`. -/
  estimate : ∀ y ∈ Y, ∀ w : Plane, planeArea w ≤ 1 →
    f y (planeArea (Return.flow (planarVF B y) 1 w)) ≤ unitRearr (f y) (planeArea w) + ξ

/-- The planar generator `B` (log-sum-exp potential with endpoint barrier and
angular wall, joint Morse chart, rotation/area normalisation, five-segment family, whole-path
normalisation, source primitive), for the slice family `sliceFn` on `bigParams`. -/
def planarGen (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) :
    Moments m → ℝ → Plane → ℝ :=
  (PlanarGen.sliceInput Δ F j (softLen Δ F j e) (faceLen Δ j) (boxRad Δ) (eta0 F j e)
    (planarTol e)).gen

/-- The explicit input of `planarGen`. -/
abbrev planarInput (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) : PlanarGen.Input m :=
  PlanarGen.sliceInput Δ F j (softLen Δ F j e) (faceLen Δ j) (boxRad Δ) (eta0 F j e)
    (planarTol e)

/-- The affine face lengths are globally smooth. -/
theorem planar_faceLen_smooth (Δ : Polytope m q) (j : Fin m) (ν : Fin q) :
    ContDiff ℝ ∞ (faceLen Δ j ν) := by
  unfold faceLen
  refine (contDiff_const.sub (ContDiff.sum fun i _ => ?_)).div_const _
  by_cases hi : i = j
  · simp only [if_pos hi]; exact contDiff_const
  · simp only [if_neg hi]; exact contDiff_const.mul (contDiff_apply ℝ ℝ i)

/-- The soft minimum is smooth globally, since a bounded polytope has a positive face
in every coordinate direction and hence its exponential sum never vanishes. -/
theorem planar_softLen_smooth {Δ : Polytope m q} (hΔ : Δ.Spec) (F : PolyFn m)
    (j : Fin m) (e : ℝ) : ContDiff ℝ ∞ (softLen Δ F j e) := by
  let E : Moments m → ℝ := fun y => ∑ ν, (if 0 < Δ.b ν j then
    Real.exp (-faceLen Δ j ν y / softTemp q F j e) else 0)
  have hE : ContDiff ℝ ∞ E := by
    apply ContDiff.sum
    intro ν _
    by_cases hν : 0 < Δ.b ν j
    · simp only [if_pos hν]
      exact (((planar_faceLen_smooth Δ j ν).neg).div_const _).exp
    · simp only [if_neg hν]; exact contDiff_const
  have hpos (y : Moments m) : 0 < E y := by
    obtain ⟨ν, hν⟩ := hΔ.bounded_dir j
    have hs := Finset.single_le_sum (s := Finset.univ)
      (f := fun μ => if 0 < Δ.b μ j then
        Real.exp (-faceLen Δ j μ y / softTemp q F j e) else 0)
      (fun μ _ => by split_ifs <;> positivity) (Finset.mem_univ ν)
    simp only [if_pos hν] at hs
    exact (Real.exp_pos _).trans_le hs
  exact (contDiff_const.mul (hE.log (fun y => (hpos y).ne'))).sub contDiff_const

/-- Uniform slice-data bounds on the parameter compact. -/
theorem planar_slice_bounds {Δ : Polytope m q} (hΔ : Δ.Spec) (F : PolyFn m)
    (j : Fin m) {e : ℝ} (he : 0 < e) {y : Moments m} (hy : y ∈ bigParams Δ F j e) :
    0 < boxRad Δ ∧ 0 < eta0 F j e ∧ 0 < softLen Δ F j e y ∧
      softLen Δ F j e y ≤ PlanarGen.lenBound Δ j (boxRad Δ) := by
  have hR : 0 < boxRad Δ := by
    unfold boxRad
    have : 0 ≤ ∑ i, ∑ ν, (if 0 < Δ.b ν i then Δ.ℓ ν / Δ.b ν i else 0) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun ν _ => by
        split_ifs with h
        · exact div_nonneg (hΔ.ℓ_pos ν).le h.le
        · exact le_rfl
    linarith
  have hη : 0 < eta0 F j e := by
    unfold eta0 slopeBound
    have : 0 ≤ (F.map fun a => |a.coef j|).sum :=
      List.sum_nonneg (by
        intro x hx; obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)
    exact div_pos he (by linarith)
  have hs : 0 < softTemp q F j e := by unfold softTemp zeta; positivity
  have hd : 0 ≤ softShift F j e := by unfold softShift zeta; positivity
  obtain ⟨μ, hμ⟩ := hΔ.bounded_dir j
  have hlo := PlanarGen.lse_ge (Δ.b · j) (faceLen Δ j · y) hs hμ (hy.2.2)
    (δ := softShift F j e)
  have hhi := PlanarGen.lse_le (Δ.b · j) (faceLen Δ j · y) hs hd hμ
  have hlen := PlanarGen.faceTerm_le_lenBound Δ j hR hy.2.1 hμ
  change 3 * eta0 F j e / 4 - softTemp q F j e * q - softShift F j e ≤
    softLen Δ F j e y at hlo
  change softLen Δ F j e y ≤ faceLen Δ j μ y at hhi
  have htemp : softTemp q F j e * q ≤ eta0 F j e / 32 := by
    unfold softTemp zeta
    have hq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hshift : softShift F j e = eta0 F j e / 32 := by unfold softShift zeta; ring
  refine ⟨hR, hη, by rw [hshift] at hlo; linarith, ?_⟩
  exact hhi.trans (by change faceLen Δ j μ y ≤ _ at hlen; linarith)

/-- On the active cutoff the slice lies in the uniform coefficient envelope. -/
theorem planar_active_bounds {Δ : Polytope m q} (hΔ : Δ.Spec) (F : PolyFn m)
    (j : Fin m) {e : ℝ} (he : 0 < e) {y : Moments m}
    (hy : (planarInput Δ F j e).cutoff y ≠ 0) :
    0 < boxRad Δ ∧ 0 < eta0 F j e ∧ (∀ i, |y i| ≤ 4 * boxRad Δ) ∧
      0 < softLen Δ F j e y ∧ softLen Δ F j e y ≤ PlanarGen.lenBound Δ j (boxRad Δ) := by
  have hR : 0 < boxRad Δ := by
    unfold boxRad
    have : 0 ≤ ∑ i, ∑ ν, (if 0 < Δ.b ν i then Δ.ℓ ν / Δ.b ν i else 0) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun ν _ => by
        split_ifs with h
        · exact div_nonneg (hΔ.ℓ_pos ν).le h.le
        · exact le_rfl
    linarith
  have hη : 0 < eta0 F j e := by
    unfold eta0 slopeBound
    have : 0 ≤ (F.map fun a => |a.coef j|).sum :=
      List.sum_nonneg (by
        intro x hx; obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)
    exact div_pos he (by linarith)
  have hcut := PlanarGen.paramCut_ne_zero_bounds hR hη hy
  have hs : 0 < softTemp q F j e := by unfold softTemp zeta; positivity
  have hd : 0 ≤ softShift F j e := by unfold softShift zeta; positivity
  obtain ⟨μ, hμ⟩ := hΔ.bounded_dir j
  have hlo := PlanarGen.lse_ge (Δ.b · j) (faceLen Δ j · y) hs hμ (fun ν hν => (hcut.2 ν hν).le)
    (δ := softShift F j e)
  have hhi := PlanarGen.lse_le (Δ.b · j) (faceLen Δ j · y) hs hd hμ
  have hlen := PlanarGen.faceTerm_le_lenBound4 Δ j hR (fun i => (hcut.1 i).le) hμ
  change eta0 F j e / 2 - softTemp q F j e * q - softShift F j e ≤ softLen Δ F j e y at hlo
  change softLen Δ F j e y ≤ faceLen Δ j μ y at hhi
  have htemp : softTemp q F j e * q ≤ eta0 F j e / 32 := by
    unfold softTemp zeta
    have hq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hshift : softShift F j e = eta0 F j e / 32 := by unfold softShift zeta; ring
  refine ⟨hR, hη, fun i => (hcut.1 i).le, ?_, ?_⟩
  · rw [hshift] at hlo
    linarith
  · exact hhi.trans (by change faceLen Δ j μ y ≤ _ at hlen; linarith)

/-- The closed parameter cutoff support stays inside the positive, uniform slice envelope. -/
theorem planar_closed_active_bounds {Δ : Polytope m q} (hΔ : Δ.Spec) (F : PolyFn m)
    (j : Fin m) {e : ℝ} (he : 0 < e) {y : Moments m}
    (hy : y ∈ tsupport (planarInput Δ F j e).cutoff) :
    0 < boxRad Δ ∧ 0 < eta0 F j e ∧ (∀ i, |y i| ≤ 4 * boxRad Δ) ∧
      0 < softLen Δ F j e y ∧ softLen Δ F j e y ≤ PlanarGen.lenBound Δ j (boxRad Δ) := by
  have hR : 0 < boxRad Δ := by
    unfold boxRad
    have : 0 ≤ ∑ i, ∑ ν, (if 0 < Δ.b ν i then Δ.ℓ ν / Δ.b ν i else 0) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun ν _ => by
        split_ifs with h
        · exact div_nonneg (hΔ.ℓ_pos ν).le h.le
        · exact le_rfl
    linarith
  have hη : 0 < eta0 F j e := by
    unfold eta0 slopeBound
    have : 0 ≤ (F.map fun a => |a.coef j|).sum :=
      List.sum_nonneg (by
        intro x hx; obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)
    exact div_pos he (by linarith)
  have hfaces : ∀ ν, Continuous (faceLen Δ j ν) :=
    fun ν => (planar_faceLen_smooth Δ j ν).continuous
  have hcut := PlanarGen.paramCut_tsupport_bounds hR hη hfaces hy
  have hs : 0 < softTemp q F j e := by unfold softTemp zeta; positivity
  have hd : 0 ≤ softShift F j e := by unfold softShift zeta; positivity
  obtain ⟨μ, hμ⟩ := hΔ.bounded_dir j
  have hlo := PlanarGen.lse_ge (Δ.b · j) (faceLen Δ j · y) hs hμ (fun ν hν => hcut.2 ν hν)
    (δ := softShift F j e)
  have hhi := PlanarGen.lse_le (Δ.b · j) (faceLen Δ j · y) hs hd hμ
  have hlen := PlanarGen.faceTerm_le_lenBound4 Δ j hR (fun i => hcut.1 i) hμ
  change eta0 F j e / 2 - softTemp q F j e * q - softShift F j e ≤ softLen Δ F j e y at hlo
  change softLen Δ F j e y ≤ faceLen Δ j μ y at hhi
  have htemp : softTemp q F j e * q ≤ eta0 F j e / 32 := by
    unfold softTemp zeta
    have hq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  have hshift : softShift F j e = eta0 F j e / 32 := by unfold softShift zeta; ring
  refine ⟨hR, hη, fun i => hcut.1 i, ?_, ?_⟩
  · rw [hshift] at hlo
    linarith
  · exact hhi.trans (by change faceLen Δ j μ y ≤ _ at hlen; linarith)

/-- The closed cutoff support lies inside the open joint-smoothness envelope. -/
theorem planar_cutoff_support_good {Δ : Polytope m q} (hΔ : Δ.Spec) {F : PolyFn m}
    (hF : F ≠ []) (j : Fin m) {e : ℝ} (he : 0 < e) :
    tsupport (planarInput Δ F j e).cutoff ⊆
      PlanarGen.sliceGood Δ j (softLen Δ F j e) (faceLen Δ j)
        (boxRad Δ) (eta0 F j e) (planarTol e) (F := F) := by
  intro y hy
  obtain ⟨hR, _, hbox, hell0, hlen⟩ := planar_closed_active_bounds hΔ F j he hy
  exact PlanarGen.sliceGood_of_box Δ hF j (planar_softLen_smooth hΔ F j e) (faceLen Δ j)
    hR.le (show 0 < planarTol e from div_pos he (by norm_num)) hbox hell0.le hlen

/-- The coefficient cutoff is smooth for every value of the external tolerance. -/
theorem planar_cutoff_smooth (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) :
    ContDiff ℝ ∞ (planarInput Δ F j e).cutoff :=
  PlanarGen.paramCut_smooth (fun ν => planar_faceLen_smooth Δ j ν)

/-- (`lem:pln-five-segment` uniformly in `y`) The five-segment path of `planarGen` is an
ordinary path at every parameter where the cutoff `ψ` is nonzero. -/
theorem planarGen_ordinary {Δ : Polytope m q} (hΔ : Δ.Spec) {F : PolyFn m} (hF : F ≠ [])
    (j : Fin m) {e : ℝ} (he : 0 < e) (y : Moments m)
    (hy : (planarInput Δ F j e).cutoff y ≠ 0) :
    Qhat.OrdinaryPath ((planarInput Δ F j e).pathData y) := by
  obtain ⟨hR, hη, hybox, hell0, hell⟩ := planar_active_bounds hΔ F j he hy
  let D := planarInput Δ F j e
  have hξ : 0 < D.xi := div_pos he (by norm_num)
  have hL : 0 ≤ D.L := PlanarGen.sliceInput_L_nonneg Δ F j _ _ hR.le _ _
  have hne : D.pieces y ≠ [] := PlanarGen.sliceInput_pieces_ne_nil Δ hF j _ _ _ _ _ y
  have hb : ∀ p ∈ D.pieces y, |p.2| ≤ D.L :=
    PlanarGen.sliceInput_slope_bound Δ F j _ _ _ _ _ y hell0.le hell
  have hbM : ∀ p ∈ D.pieces y, |p.1| + |p.2| ≤ D.M :=
    PlanarGen.sliceInput_value_bound Δ F j _ _ hR.le _ _ y hybox hell0.le hell
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
  have hM : 0 ≤ D.M := (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hbM p hp)
  have hv := D.vstar_uniform_bounds y hξ hL hne hb
  have ha := D.alphaU_bounds y hξ hL hne hb
  apply PlanarGen.Input.ordinary_of_yhyp (D := D) (y := y)
  exact ⟨hξ, hL, hM, D.b0_pos_of_pieces y hξ hL hne hb, hv.1, hv.2, ha.1, ha.2,
    D.innerHyp y hξ hL hne hb hbM⟩

/-- (Parameter dependence) `planarGen` is jointly `C^∞` in `(y, s, w)`. -/
theorem planarGen_smooth {Δ : Polytope m q} (hΔ : Δ.Spec) {F : PolyFn m} (hF : F ≠ [])
    (j : Fin m) {e : ℝ} (he : 0 < e) :
    ContDiff ℝ ∞ (fun x : Moments m × ℝ × Plane => planarGen Δ F j e x.1 x.2.1 x.2.2) := by
  let D := planarInput Δ F j e
  let U := PlanarGen.sliceGood Δ j (softLen Δ F j e) (faceLen Δ j)
    (boxRad Δ) (eta0 F j e) (planarTol e) (F := F)
  have hR : 0 ≤ boxRad Δ := by
    unfold boxRad
    have hs : 0 ≤ ∑ i, ∑ ν, (if 0 < Δ.b ν i then Δ.ℓ ν / Δ.b ν i else 0) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun ν _ => by
        split_ifs with h
        · exact div_nonneg (hΔ.ℓ_pos ν).le h.le
        · exact le_rfl
    linarith
  have hξ : 0 < planarTol e := div_pos he (by norm_num)
  have hℓ := planar_softLen_smooth hΔ F j e
  have hU : IsOpen U := PlanarGen.sliceGood_open Δ hF j hℓ (faceLen Δ j) hR hξ
  have hO : ∀ y ∈ U, Qhat.OrdinaryPath
      (PlanarGen.varyPath (D.pathData 0) D.ordPath y) := by
    intro y hy
    exact PlanarGen.slice_ordinary Δ hF j hℓ (faceLen Δ j) hR hξ hy
  have hpath : ContDiffOn ℝ ∞ (fun p : (Moments m × ℝ) × ℂ =>
      D.ordPath p.1.1 p.1.2 p.2) ((U ×ˢ univ) ×ˢ Qhat.areaDisk (D.pathData 0).pdag) :=
    PlanarGen.slice_ordPath_joint Δ hF j hℓ (faceLen Δ j) hR hξ
  have hraw : ContDiffOn ℝ ∞ (fun p : (Moments m × ℝ) × ℂ =>
      Qhat.Qham (D.pathData p.1.1) p.1.2 p.2) ((U ×ˢ univ) ×ˢ univ) :=
    PlanarGen.varying_Qham_smooth (D := D.pathData 0) (f := D.ordPath) (U := U) hU hO hpath
  have hc := planar_cutoff_smooth Δ F j e
  have hgen := PlanarGen.cutoff_rescaled_family_smooth
    (χ := D.cutoff) (U := U) (B := fun y t z => Qhat.Qham (D.pathData y) t z) hc hU
    (planar_cutoff_support_good hΔ hF j he) hraw
  have hmap : ContDiff ℝ ∞ (fun x : Moments m × ℝ × Plane =>
      (x.1, x.2.1, PlanarGen.cplx x.2.2)) :=
    contDiff_fst.prodMk ((contDiff_fst.comp contDiff_snd).prodMk
      (PlanarGen.cplx.contDiff.comp (contDiff_snd.comp contDiff_snd)))
  simpa only [planarGen, PlanarGen.Input.gen, PlanarGen.Input.rawGen,
    Function.comp_def, PlanarGen.cplx_apply] using hgen.comp hmap

/-- (Endpoint estimate; the analogue of `Branch2.Planar.Hyp.planarPath_comparison`)
On the parameter compact, `q̂_1` of the five-segment path realises the rearrangement of the
slice up to `ξ` on the closed disc of capacity `1`. -/
theorem planarGen_endpoint {Δ : Polytope m q} (hΔ : Δ.Spec) {F : PolyFn m} (hF : F ≠ [])
    (j : Fin m) {e : ℝ} (he : 0 < e) (y : Moments m) (hy : y ∈ bigParams Δ F j e) (z : ℂ)
    (hz : Real.pi * ‖z‖ ^ 2 ≤ 1) :
    sliceFn Δ F j e y (Real.pi * ‖Qhat.qhat ((planarInput Δ F j e).pathData y) 1 z‖ ^ 2) ≤
      unitRearr (sliceFn Δ F j e y) (Real.pi * ‖z‖ ^ 2) + planarTol e := by
  obtain ⟨hR, hη, hell0, hell⟩ := planar_slice_bounds hΔ F j he hy
  let D := planarInput Δ F j e
  have hξ : 0 < planarTol e := div_pos he (by norm_num)
  have hL : 0 ≤ D.L := PlanarGen.sliceInput_L_nonneg Δ F j _ _ hR.le _ _
  have hc : D.cutoff y = 1 := PlanarGen.paramCut_eq_one hR hη hy.2.1 hy.2.2
  have hO := planarGen_ordinary hΔ hF j he y (by rw [hc]; exact one_ne_zero)
  have hsum : 0 ≤ (F.map fun a => |a.coef j|).sum :=
    List.sum_nonneg (by
      intro x hx; obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)
  let K := (F.map fun a => |a.coef j|).sum * |softLen Δ F j e y|
  have hK : 0 ≤ K := mul_nonneg hsum (abs_nonneg _)
  have hKL : K ≤ D.L := by
    dsimp only [K, D, planarInput, PlanarGen.sliceInput]
    rw [abs_of_pos hell0]
    have := mul_le_mul_of_nonneg_left hell hsum
    linarith
  exact D.endpoint_of_inner hO hξ hL hK hKL
    (fun a _ b _ => PlanarGen.slice_lip F j y _ a b)
    (fun v hv => PlanarGen.slice_le_max hF j y _ hv)
    (fun w hw => PlanarGen.sliceInput_inner Δ hF j _ _ hR hξ hy.1 hy.2.1 hell0.le hell w hw)
    z hz

theorem planarGen_spec {Δ : Polytope m q} (hΔ : Δ.Spec) {F : PolyFn m} (hF : F ≠ [])
    (j : Fin m) {e : ℝ} (he : 0 < e) :
    PlanarSpec (sliceFn Δ F j e) (bigParams Δ F j e) (planarTol e) (planarGen Δ F j e) := by
  set D := planarInput Δ F j e with hDdef
  refine ⟨planarGen_smooth hΔ hF j he, ?_, ?_⟩
  · obtain ⟨rB, hrB, h⟩ := D.gen_support (planarGen_ordinary hΔ hF j he)
    exact ⟨rB, hrB, fun y s w hw => h y s w hw⟩
  · intro y hy w hw
    have hR : 0 < boxRad Δ := by
      unfold boxRad
      have : 0 ≤ ∑ i, ∑ ν, (if 0 < Δ.b ν i then Δ.ℓ ν / Δ.b ν i else 0) :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun ν _ => by
          split_ifs with h
          · exact div_nonneg (hΔ.ℓ_pos ν).le h.le
          · exact le_rfl
      linarith
    have hη : 0 < eta0 F j e := by
      unfold eta0 slopeBound
      have : 0 ≤ (F.map fun a => |a.coef j|).sum :=
        List.sum_nonneg (by
          intro x hx; obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)
      exact div_pos he (by linarith)
    have hc : D.cutoff y = 1 := PlanarGen.paramCut_eq_one hR hη hy.2.1 hy.2.2
    have hO := planarGen_ordinary hΔ hF j he y (by rw [hc]; exact one_ne_zero)
    have hB : ∀ s, planarGen Δ F j e y s =
        fun u : Plane => Qhat.Qham (D.pathData y) s ⟨u.1, u.2⟩ := by
      intro s; funext u
      show D.gen y s u = _
      rw [PlanarGen.Input.gen, hc, one_mul, one_mul]
      rfl
    have hVF : planarVF (planarGen Δ F j e) y = PlanarGen.qField (D.pathData y) := by
      funext s v; simp only [planarVF, hB, PlanarGen.qField]
    rw [hVF, PlanarGen.flow_qField hO]
    have harea : planeArea w = Real.pi * ‖(⟨w.1, w.2⟩ : ℂ)‖ ^ 2 := (PlanarGen.area_mk w).symm
    have harea' : ∀ z : ℂ, planeArea (z.re, z.im) = Real.pi * ‖z‖ ^ 2 := by
      intro z; unfold planeArea; rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [harea', harea]
    exact planarGen_endpoint hΔ hF j he y hy _ (by rw [← harea]; exact hw)

/-! ### The lift -/

/-- The other moments of `z` (coordinate `j` set to `0`). -/
def otherMoments (j : Fin m) (z : Fibre m) : Moments m :=
  Function.update (planeMoments z) j 0

/-- **The lifted generator** `Q(t,z) = χ(y) S'(t) ℓ(y) B(y, χ(y) S(t), z_j/√ℓ(y))`. -/
def liftGen (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) (t : ℝ) (z : Fibre m) : ℝ :=
  cut Δ F j e (otherMoments j z) * deriv Real.smoothTransition t *
    softLen Δ F j e (otherMoments j z) *
    planarGen Δ F j e (otherMoments j z)
      (cut Δ F j e (otherMoments j z) * Real.smoothTransition t)
      ((Real.sqrt (softLen Δ F j e (otherMoments j z)))⁻¹ • z j)

/-! ### Elementary facts -/

theorem slopeBound_pos (F : PolyFn m) (j : Fin m) : 0 < slopeBound F j := by
  unfold slopeBound
  have : 0 ≤ (F.map fun a => |a.coef j|).sum :=
    List.sum_nonneg (by intro x hx; obtain ⟨a, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _)
  linarith

theorem eta0_pos (F : PolyFn m) (j : Fin m) {e : ℝ} (he : 0 < e) : 0 < eta0 F j e :=
  div_pos he (by linarith [slopeBound_pos F j])

theorem zeta_pos (F : PolyFn m) (j : Fin m) {e : ℝ} (he : 0 < e) : 0 < zeta F j e :=
  div_pos (eta0_pos F j he) (by norm_num)

theorem softTemp_pos (F : PolyFn m) (j : Fin m) {e : ℝ} (he : 0 < e) :
    0 < softTemp q F j e :=
  div_pos (zeta_pos F j he) (by positivity)

theorem softShift_pos (F : PolyFn m) (j : Fin m) {e : ℝ} (he : 0 < e) :
    0 < softShift F j e :=
  div_pos (zeta_pos F j he) (by norm_num)

end SymplecticPacking.HighDim.RealiseGen
