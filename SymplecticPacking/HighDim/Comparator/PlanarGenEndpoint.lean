import SymplecticPacking.HighDim.Comparator.PlanarGen
import SymplecticPacking.HighDim.Comparator.PlanarSliceComparison

/-!
# Endpoint estimate of the planar generator (supporting lemmas for `RealiseGen.planarGen_endpoint`)

Reduction of the endpoint estimate of the five-segment path `PlanarGen.Input.pathData y`
(the analogue of
`Branch2.Planar.PlanarInput.Hyp.planarPath_comparison`):

* `Input.ordPath_one`: at time `1` the five-segment path is the inner family `q_{y,1}`
  (the linear segment ends at `M_{y,1} = A₀(y)`);
* `rearrInf_ge`: `max(g 0, g 1) - K(1 - I) ≤ (R g)(I)` for a `K`-Lipschitz `g` on `[0,1]`;
* `Input.endpoint_of_inner`: for an ordinary path, the estimate on the whole closed unit disc
  follows from the inner estimate on `{π|z|² ≤ 1 - 8η}`; on the outer annulus it follows from
  `q̂₁(D̄(1)) = D̄(1)`, `g ≤ max(g 0, g 1)` and `8ηL ≤ ξ`;
* slice facts (`slice_lip`, `slice_le_max`) and the soft-min bounds (`lse_le`, `lse_ge`,
  `faceTerm_le_lenBound`) used to check the hypotheses for the polytope slice family;
* `sliceInput_inner`: the inner estimate `F(π|q_{y,1}(z)|²) ≤ (R F)(π|z|²) + ξ`
  (the single-parameter Morse/area argument).
-/

noncomputable section

namespace SymplecticPacking.HighDim.PlanarGen

open Set Complex
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped Real

variable {m q : ℕ}

/-! ### The path at time one -/

namespace Input

variable (D : Input m)

theorem clock_one {j : ℕ} (hj : j ≤ 4) : clock j 1 = 1 := by
  unfold clock
  apply Real.smoothTransition.one_of_one_le
  have : (j : ℝ) ≤ 4 := by exact_mod_cast hj
  linarith

theorem b0_nonneg : 0 ≤ D.b0 := by
  unfold b0 Branch2.Planar.Well.lin
  exact one_div_nonneg.2 (Real.sqrt_nonneg _)

theorem A11_nonpos (y : Moments m) : D.A11 y ≤ 0 := by
  unfold A11 cx rb a0
  have h1 : 0 ≤ √(2 / D.alphaU y) / √(D.j0 y) := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h2 : 0 ≤ 2 * π * √(D.vstar y / π) := by positivity
  have := div_nonneg h1 h2
  linarith

theorem A22_nonpos (y : Moments m) : D.A22 y ≤ 0 := by
  unfold A22 cy rb
  have h1 : 0 ≤ D.b0 / √(D.j0 y) := div_nonneg D.b0_nonneg (Real.sqrt_nonneg _)
  have h2 : 0 ≤ 2 * π * √(D.vstar y / π) := by positivity
  have := mul_nonneg h2 h1
  linarith

/-- The linear segment ends at `A₀(y)`: `M_{y,1} = Rot_π diag(|A₁₁|, |A₂₂|) = diag(A₁₁, A₂₂)`. -/
theorem Msig_one (y : Moments m) (z : ℂ) : D.Msig y 1 z = D.A0 y z := by
  unfold Msig A0 Inner.Rot
  have hexp : Complex.exp (((π * 1 : ℝ) : ℂ) * I) = -1 := by
    rw [mul_one, Complex.exp_pi_mul_I]
  rw [hexp, Real.rpow_one, Real.rpow_one, abs_of_nonpos (D.A11_nonpos y),
    abs_of_nonpos (D.A22_nonpos y)]
  push_cast
  ring

/-- At time `1` the five-segment path is the inner family `q_{y,1}`. -/
theorem ordPath_one (y : Moments m) (z : ℂ) : D.ordPath y 1 z = D.qin y 1 z := by
  unfold ordPath
  rw [clock_one (j := 0) (by norm_num), clock_one (j := 1) (by norm_num),
    clock_one (j := 2) (by norm_num), clock_one (j := 3) (by norm_num),
    clock_one (j := 4) (by norm_num), Real.rpow_one, sub_self, Real.rpow_zero, D.Msig_one]
  push_cast
  ring

/-- `8ηL ≤ ξ`. -/
theorem eta_mul_le (hξ : 0 < D.xi) (hL : 0 ≤ D.L) : D.L * (8 * D.eta) ≤ D.xi := by
  have h1 : D.eta ≤ D.xi / (32 * (D.L + 1)) / 2 := by
    unfold eta
    linarith [min_le_right (1 / 16 : ℝ) (D.xi / (32 * (D.L + 1)))]
  have h2 : D.L * (D.xi / (32 * (D.L + 1))) ≤ D.xi / 32 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h3 := mul_le_mul_of_nonneg_left h1 hL
  have e1 : D.L * (D.xi / (32 * (D.L + 1)) / 2) = D.L * (D.xi / (32 * (D.L + 1))) / 2 := by ring
  have e2 : D.L * (8 * D.eta) = 8 * (D.L * D.eta) := by ring
  rw [e2]
  linarith

end Input

/-! ### A lower bound for the rearrangement -/

/-- `max(g 0, g 1) - K(1 - I) ≤ inf_{0 ≤ a ≤ 1-I} max(g a, g(a + I))` for `K`-Lipschitz `g`. -/
theorem rearrInf_ge {g : ℝ → ℝ} {K I : ℝ} (hK : 0 ≤ K)
    (hlip : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, |g a - g b| ≤ K * |a - b|)
    (hI : I ∈ Icc (0 : ℝ) 1) :
    max (g 0) (g 1) - K * (1 - I) ≤ ⨅ a : Icc (0 : ℝ) (1 - I), max (g a) (g (a + I)) := by
  haveI : Nonempty (Icc (0 : ℝ) (1 - I)) := ⟨⟨0, le_rfl, by linarith [hI.2]⟩⟩
  refine le_ciInf fun a => ?_
  obtain ⟨a, ha0, ha1⟩ := a
  have hA : a ∈ Icc (0 : ℝ) 1 := ⟨ha0, by linarith [hI.1]⟩
  have hB : a + I ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hI.1], by linarith⟩
  have l1 := hlip 0 ⟨le_rfl, zero_le_one⟩ a hA
  have l2 := hlip 1 ⟨zero_le_one, le_rfl⟩ (a + I) hB
  rw [zero_sub, abs_neg, abs_of_nonneg ha0] at l1
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - (a + I))] at l2
  have e1 : K * a ≤ K * (1 - I) := mul_le_mul_of_nonneg_left (by linarith) hK
  have e2 : K * (1 - (a + I)) ≤ K * (1 - I) := mul_le_mul_of_nonneg_left (by linarith) hK
  have m1 := le_max_left (g a) (g (a + I))
  have m2 := le_max_right (g a) (g (a + I))
  rw [sub_le_iff_le_add]
  exact max_le (by linarith [(abs_le.mp l1).2]) (by linarith [(abs_le.mp l2).2])

/-! ### Reduction to the inner estimate -/

namespace Input

variable (D : Input m)

/-- **Endpoint estimate from the inner estimate.** For an ordinary path, a `K`-Lipschitz
(`K ≤ L`) function `g` with `g ≤ max(g 0, g 1)` on `[0,1]` satisfying the estimate for `q_{y,1}`
on `{π|z|² ≤ 1 - 8η}` satisfies it for `q̂₁` on the whole closed unit disc. -/
theorem endpoint_of_inner {y : Moments m} (hO : Qhat.OrdinaryPath (D.pathData y))
    (hξ : 0 < D.xi) (hL : 0 ≤ D.L) {g : ℝ → ℝ} {K : ℝ} (hK0 : 0 ≤ K) (hKL : K ≤ D.L)
    (hlip : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, |g a - g b| ≤ K * |a - b|)
    (hmax : ∀ v ∈ Icc (0 : ℝ) 1, g v ≤ max (g 0) (g 1))
    (hinner : ∀ z : ℂ, π * ‖z‖ ^ 2 ≤ 1 - 8 * D.eta →
      g (π * ‖D.qin y 1 z‖ ^ 2) ≤
        (⨅ a : Icc (0 : ℝ) (1 - π * ‖z‖ ^ 2), max (g a) (g (a + π * ‖z‖ ^ 2))) + D.xi)
    (z : ℂ) (hz : π * ‖z‖ ^ 2 ≤ 1) :
    g (π * ‖Qhat.qhat (D.pathData y) 1 z‖ ^ 2) ≤
      (⨅ a : Icc (0 : ℝ) (1 - π * ‖z‖ ^ 2), max (g a) (g (a + π * ‖z‖ ^ 2))) + D.xi := by
  have hη := eta_pos hξ hL
  rcases le_or_gt (π * ‖z‖ ^ 2) (1 - 8 * D.eta) with h1 | h1
  · have hq : Qhat.qhat (D.pathData y) 1 z = (D.pathData y).path 1 z :=
      (Qhat.qhat_interface hO).2.2.2.2.2.2.2.2.2.2.2.2 z
        (by show π * ‖z‖ ^ 2 ≤ 1 - 4 * (2 * D.eta); linarith)
    rw [hq]
    show g (π * ‖D.ordPath y 1 z‖ ^ 2) ≤ _
    rw [D.ordPath_one]
    exact hinner z h1
  · have hmem : Qhat.qhat (D.pathData y) 1 z ∈ Qhat.closedAreaDisk (D.pathData y).h := by
      have := Qhat.qhat_disk hO (P := (D.pathData y).h) hO.Psupp_lt_h.le 1
      rw [← this]
      exact ⟨z, hz, rfl⟩
    have hP : π * ‖Qhat.qhat (D.pathData y) 1 z‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨by positivity, hmem⟩
    have hF1 := hmax _ hP
    have hF2 := rearrInf_ge hK0 hlip (I := π * ‖z‖ ^ 2) ⟨by positivity, hz⟩
    have hb : K * (1 - π * ‖z‖ ^ 2) ≤ D.L * (8 * D.eta) :=
      (mul_le_mul_of_nonneg_left (by linarith) hK0).trans
        (mul_le_mul_of_nonneg_right hKL (by linarith))
    linarith [D.eta_mul_le hξ hL]

end Input

/-! ### Slices of a convex piecewise-affine function -/

theorem slice_sub_le {F : PolyFn m} (hF : F ≠ []) (j : Fin m) (y : Moments m) (lam a b : ℝ) :
    PolyFn.eval F (Function.update y j (lam * a)) - PolyFn.eval F (Function.update y j (lam * b))
      ≤ (F.map fun c => |c.coef j|).sum * |lam| * |a - b| := by
  obtain ⟨c, hc, he⟩ := PolyFn.eval_mem hF (Function.update y j (lam * a))
  have h2 := PolyFn.le_eval hc (Function.update y j (lam * b))
  rw [he, AffinePiece.eval_update]
  rw [AffinePiece.eval_update] at h2
  have hcS : |c.coef j| ≤ (F.map fun c => |c.coef j|).sum :=
    List.single_le_sum (fun x hx => by
      obtain ⟨d, -, rfl⟩ := List.mem_map.mp hx; exact abs_nonneg _) _
      (List.mem_map.mpr ⟨c, hc, rfl⟩)
  have h3 : c.coef j * (lam * a) - c.coef j * (lam * b) ≤ |c.coef j| * |lam| * |a - b| := by
    have e : c.coef j * (lam * a) - c.coef j * (lam * b) = c.coef j * (lam * (a - b)) := by ring
    rw [e, mul_assoc]
    exact (le_abs_self _).trans (le_of_eq (by rw [abs_mul, abs_mul]))
  have h4 : |c.coef j| * |lam| * |a - b| ≤ (F.map fun c => |c.coef j|).sum * |lam| * |a - b| :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcS (abs_nonneg _)) (abs_nonneg _)
  linarith

/-- The slice `v ↦ F(y + λ v e_j)` is `(Σ_r |∂_j ℓ_r|) |λ|`-Lipschitz. -/
theorem slice_lip (F : PolyFn m) (j : Fin m) (y : Moments m) (lam a b : ℝ) :
    |PolyFn.eval F (Function.update y j (lam * a)) -
        PolyFn.eval F (Function.update y j (lam * b))|
      ≤ (F.map fun c => |c.coef j|).sum * |lam| * |a - b| := by
  by_cases hF : F = []
  · subst hF
    simp only [PolyFn.eval, sub_self, abs_zero, List.map_nil, List.sum_nil, zero_mul, le_refl]
  refine abs_sub_le_iff.mpr ⟨slice_sub_le hF j y lam a b, ?_⟩
  rw [abs_sub_comm a b]
  exact slice_sub_le hF j y lam b a

/-- A convex slice is below the maximum of its endpoint values on `[0,1]`. -/
theorem slice_le_max {F : PolyFn m} (hF : F ≠ []) (j : Fin m) (y : Moments m) (lam : ℝ)
    {v : ℝ} (hv : v ∈ Icc (0 : ℝ) 1) :
    PolyFn.eval F (Function.update y j (lam * v)) ≤
      max (PolyFn.eval F (Function.update y j (lam * 0)))
        (PolyFn.eval F (Function.update y j (lam * 1))) := by
  obtain ⟨c, hc, he⟩ := PolyFn.eval_mem hF (Function.update y j (lam * v))
  have h0 := PolyFn.le_eval hc (Function.update y j (lam * 0))
  have h1 := PolyFn.le_eval hc (Function.update y j (lam * 1))
  have m0 := le_max_left (PolyFn.eval F (Function.update y j (lam * 0)))
    (PolyFn.eval F (Function.update y j (lam * 1)))
  have m1 := le_max_right (PolyFn.eval F (Function.update y j (lam * 0)))
    (PolyFn.eval F (Function.update y j (lam * 1)))
  rw [he, AffinePiece.eval_update]
  rw [AffinePiece.eval_update] at h0 h1
  have e : c.coef j * (lam * v) + (c.zeroAt j).eval y =
      (1 - v) * (c.coef j * (lam * 0) + (c.zeroAt j).eval y) +
        v * (c.coef j * (lam * 1) + (c.zeroAt j).eval y) := by ring
  rw [e]
  nlinarith [mul_nonneg (sub_nonneg.2 hv.2) (sub_nonneg.2 (h0.trans m0)),
    mul_nonneg hv.1 (sub_nonneg.2 (h1.trans m1))]

/-! ### Soft-min bounds -/

/-- The log-sum-exp sum `Σ_{ν : b_ν > 0} exp(-L_ν/s)`. -/
def lseSum (b Lv : Fin q → ℝ) (s : ℝ) : ℝ :=
  ∑ ν, (if 0 < b ν then Real.exp (-Lv ν / s) else 0)

theorem single_le_lseSum (b Lv : Fin q → ℝ) (s : ℝ) {μ : Fin q} (hμ : 0 < b μ) :
    Real.exp (-Lv μ / s) ≤ lseSum b Lv s := by
  have := Finset.single_le_sum (f := fun ν => if 0 < b ν then Real.exp (-Lv ν / s) else 0)
    (fun ν _ => by split_ifs <;> positivity) (Finset.mem_univ μ)
  simpa only [hμ, if_true, lseSum] using this

/-- The soft minimum is below every face value. -/
theorem lse_le (b Lv : Fin q → ℝ) {s δ : ℝ} (hs : 0 < s) (hδ : 0 ≤ δ) {μ : Fin q}
    (hμ : 0 < b μ) : -s * Real.log (lseSum b Lv s) - δ ≤ Lv μ := by
  have hle := single_le_lseSum b Lv s hμ
  have hlog : -Lv μ / s ≤ Real.log (lseSum b Lv s) := by
    rw [← Real.log_exp (-Lv μ / s)]
    exact Real.log_le_log (Real.exp_pos _) hle
  have h2 := mul_le_mul_of_nonneg_left hlog hs.le
  have e : s * (-Lv μ / s) = -Lv μ := by field_simp
  rw [e] at h2
  nlinarith

/-- The soft minimum is at least `min - s q - δ`. -/
theorem lse_ge (b Lv : Fin q → ℝ) {s δ mm : ℝ} (hs : 0 < s) {μ : Fin q} (hμ : 0 < b μ)
    (hm : ∀ ν, 0 < b ν → mm ≤ Lv ν) :
    mm - s * q - δ ≤ -s * Real.log (lseSum b Lv s) - δ := by
  have hpos : 0 < lseSum b Lv s :=
    lt_of_lt_of_le (Real.exp_pos _) (single_le_lseSum b Lv s hμ)
  have hq : (0 : ℝ) < q := Nat.cast_pos.2 (Nat.zero_lt_of_lt μ.isLt)
  have hle : lseSum b Lv s ≤ q * Real.exp (-mm / s) := by
    unfold lseSum
    calc (∑ ν, (if 0 < b ν then Real.exp (-Lv ν / s) else 0))
        ≤ ∑ _ν : Fin q, Real.exp (-mm / s) := Finset.sum_le_sum fun ν _ => by
          split_ifs with h
          · exact Real.exp_le_exp.2 (div_le_div_of_nonneg_right (by linarith [hm ν h]) hs.le)
          · exact (Real.exp_pos _).le
      _ = q * Real.exp (-mm / s) := by simp
  have hlog : Real.log (lseSum b Lv s) ≤ q - mm / s := by
    have h1 := Real.log_le_log hpos hle
    rw [Real.log_mul hq.ne' (Real.exp_pos _).ne', Real.log_exp] at h1
    have h2 := Real.log_le_sub_one_of_pos hq
    have : -mm / s = -(mm / s) := neg_div _ _
    linarith
  have h3 := mul_le_mul_of_nonneg_left hlog hs.le
  have e : s * (q - mm / s) = s * q - mm := by field_simp
  rw [e] at h3
  nlinarith

/-- A face value on the box `‖y‖_∞ ≤ 3R` is below `lenBound - 1`. -/
theorem faceTerm_le_lenBound (Δ : Polytope m q) (j : Fin m) {R : ℝ} (hR : 0 < R)
    {y : Moments m} (hy : ∀ i, |y i| ≤ 3 * R) {μ : Fin q} (hμ : 0 < Δ.b μ j) :
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
        have h3 : |Δ.b μ i| * |y i| ≤ |Δ.b μ i| * (3 * R) :=
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

/-! ### The inner estimate (remaining) -/

/-- **Inner endpoint estimate** (the parameterised analogue of
`Branch2.Planar.inner_comparison`). For a parameter on the box with nonnegative slice length
`ℓ(y) ≤ lenBound`, the endpoint `q_{y,1} = C_y ∘ f_{y,1}` of the inner family realises the
rearrangement of the slice `v ↦ F(y + ℓ(y) v e_j)` up to `ξ` on `{π|z|² ≤ 1 - 8η}`.

The proof uses the modified-well area bridge, the original finite-area
normalizer, and the explicit softmax error bound. The smoothed core error is at most
`23ξ/64`, and passing to the affine slice costs at most another `ξ/64`. -/
theorem sliceInput_inner (Δ : Polytope m q) {F : PolyFn m} (hF : F ≠ []) (j : Fin m)
    (ell : Moments m → ℝ) (Lν : Fin q → Moments m → ℝ) {R η₀ ξ : ℝ} (hR : 0 < R) (hξ : 0 < ξ)
    {y : Moments m} (hy0 : y j = 0) (hy : ∀ i, |y i| ≤ 3 * R) (hell0 : 0 ≤ ell y)
    (hell : ell y ≤ lenBound Δ j R) (z : ℂ)
    (hz : π * ‖z‖ ^ 2 ≤ 1 - 8 * (sliceInput Δ F j ell Lν R η₀ ξ).eta) :
    PolyFn.eval F (Function.update y j
        (ell y * (π * ‖(sliceInput Δ F j ell Lν R η₀ ξ).qin y 1 z‖ ^ 2))) ≤
      (⨅ a : Icc (0 : ℝ) (1 - π * ‖z‖ ^ 2),
        max (PolyFn.eval F (Function.update y j (ell y * a)))
          (PolyFn.eval F (Function.update y j (ell y * (a + π * ‖z‖ ^ 2))))) + ξ := by
  let D := sliceInput Δ F j ell Lν R η₀ ξ
  have hL : 0 ≤ D.L := sliceInput_L_nonneg Δ F j _ _ hR.le _ _
  have hη := Input.eta_pos hξ hL (D := D)
  have hI : π * ‖z‖ ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨by positivity, by linarith⟩
  have hg : Continuous (fun v => PolyFn.eval F (Function.update y j (ell y * v))) :=
    (PolyFn.eval_continuous F).comp (by fun_prop)
  have hc := sliceInput_core_comparison Δ hF j ell Lν hR hξ
    (fun i => (hy i).trans (by linarith : 3 * R ≤ 4 * R)) hell0 hell hz
  rw [rearr_eq_iInf hg.continuousOn hI] at hc
  exact hc.le

end SymplecticPacking.HighDim.PlanarGen
