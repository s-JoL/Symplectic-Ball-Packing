import SymplecticPacking.General.CompileBernstein
import SymplecticPacking.General.CompileSupport

/-!
# Finite compilation in dimension `2n` (Theorem `thm:eff-finite`, supplement `sec:cpl`)

For a smooth Hamiltonian `H : ℝ × ℝ^{2n} → ℝ` and a *compilation datum* (C1)–(C7) — numbers
satisfying exactly the inequalities listed in the paper — the finite Hamiltonian
`H_fin = β_B · P`, with `P ∈ ℚ[t, z]` the rounded tensor Bernstein polynomial of `H` on the box
`[0,1] × [-B,B]^{2n}`, satisfies `PackingSpec n k C c s`.

The data and hypotheses:
* (C1) `0 < C₀ < C`, and every integral curve of `X_H` on `[0,1]` starting in a closed source ball
  ends in the closed ball `B(C₀)`;
* (C2) `S_box > 0` with `H(t,z) = 0` whenever `max_l |z_l| ≥ S_box`, and an integer
  `B > max(2n, 2 S_box)`;
* (C3) `L_X ≥ 1 + ‖D²_z H(t,z)‖` for `t ∈ [0,1]` and all `z`; `C_β ≥ 1 + ‖∇β_B(z)‖` for all `z`;
* (C4) `0 < b_R < (R_C - R₀)/4`, `R₀ = √(C₀/π)`, `R_C = √(C/π)`; `η = b_R e^{-L_X}/2`;
* (C5) `M₀ ≥ 1` bounds all first and second partial derivatives of
  `H̃(ξ) = H(ξ₀, 2Bξ₁ - B, …, 2Bξ_{2n} - B)` on `[0,1]^{2n+1}`;
* (C6) `0 < δ < min(1/2, η/(16(1+C_β)))` and an integer `N > max(1, ((2n+1)M₀/δ)², 4M₀/δ)`;
* (C7) rationals `H̃_m` with `|H̃_m - H̃(m/N)| < δ/(2N+1)` for all `m ∈ {0,…,N}^{2n+1}`.

Main results: `CompilationDatum`, `finite_spec` (the general theorem),
`image_of_packingSpec` ((C1) from `PackingSpec n k C₀ c s H`, so the target is enlarged from
`C₀` to `C`), and the intermediate estimates `poly_error`, `field_error`,
`flow_error`.
-/

noncomputable section

namespace SymplecticPacking.General.Compile

open Finset Real Set Filter Problem Metric
open scoped ContDiff Topology NNReal

variable {n : ℕ}

/-! ### The finite form `β_B · P` -/

/-- Normalising chart `Φ_B(t,z) = (t, (z_1+B)/(2B), …, (z_{2n}+B)/(2B))`. -/
def phiB (n : ℕ) (B t : ℝ) (z : E n) : Fin (2 * n + 1) → ℝ :=
  Fin.cons t fun l => (z l + B) / (2 * B)

/-- `H̃(ξ) = H(ξ₀, 2Bξ₁ - B, …, 2Bξ_{2n} - B)`, the function of (C5). -/
def Htilde (n : ℕ) (B : ℝ) (H : ℝ → E n → ℝ) (ξ : Fin (2 * n + 1) → ℝ) : ℝ :=
  H (ξ 0) (WithLp.toLp 2 fun l : Fin (2 * n) => 2 * B * ξ l.succ - B)

/-- The affine coordinates of `Φ_B` as rational polynomials. -/
def affVar (n B : ℕ) (i : Fin (2 * n + 1)) : MvPolynomial (Fin (2 * n + 1)) ℚ :=
  Fin.cases (MvPolynomial.X 0)
    (fun l => MvPolynomial.C (1 / (2 * (B : ℚ))) * (MvPolynomial.X l.succ + MvPolynomial.C (B : ℚ)))
    i

/-- The Bernstein basis polynomial evaluated at a polynomial `Y`. -/
def bPoly {σ : Type*} (N a : ℕ) (Y : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  (N.choose a : MvPolynomial σ ℚ) * Y ^ a * (1 - Y) ^ (N - a)

/-- The polynomial `P(t,z) = Σ_m H̃_m b_{N,m₀}(t) ∏_l b_{N,m_l}((z_l+B)/(2B))` of (C7). -/
def bernsteinMvPoly (n N B : ℕ) (Hm : (Fin (2 * n + 1) → Fin (N + 1)) → ℚ) :
    MvPolynomial (Fin (2 * n + 1)) ℚ :=
  ∑ m, MvPolynomial.C (Hm m) * ∏ i, bPoly N (m i) (affVar n B i)

/-- Evaluation of a rational polynomial in `(t, z₁, …, z_{2n})`. -/
def evalPoly (P : MvPolynomial (Fin (2 * n + 1)) ℚ) (t : ℝ) (z : E n) : ℝ :=
  MvPolynomial.eval (Fin.cons t fun l : Fin (2 * n) => z l) (P.map (algebraMap ℚ ℝ))

/-- The finite output `H_fin = β_B · P`. -/
def finiteHam (n : ℕ) (B : ℕ) (P : MvPolynomial (Fin (2 * n + 1)) ℚ) (t : ℝ) (z : E n) : ℝ :=
  boxCut n B z * evalPoly P t z

lemma eval_affVar (B : ℕ) (hB : (B : ℝ) ≠ 0) (t : ℝ) (z : E n) (i : Fin (2 * n + 1)) :
    MvPolynomial.eval (Fin.cons t fun l : Fin (2 * n) => z l)
      (MvPolynomial.map (algebraMap ℚ ℝ) (affVar n B i)) = phiB n B t z i := by
  refine Fin.cases ?_ (fun l => ?_) i
  · simp [affVar, phiB]
  · simp [affVar, phiB]
    field_simp

lemma evalPoly_bernsteinMvPoly (N B : ℕ) (hB : (B : ℝ) ≠ 0)
    (Hm : (Fin (2 * n + 1) → Fin (N + 1)) → ℚ) (t : ℝ) (z : E n) :
    evalPoly (bernsteinMvPoly n N B Hm) t z = Pn N (fun m => (Hm m : ℝ)) (phiB n B t z) := by
  unfold evalPoly bernsteinMvPoly Pn W
  simp only [map_sum, map_mul, map_prod, bPoly, map_pow, map_sub, map_one, map_natCast,
    MvPolynomial.map_C, MvPolynomial.eval_C, eval_affVar B hB]
  refine sum_congr rfl fun m _ => ?_
  congr 1
  all_goals first
    | exact prod_congr rfl fun i _ => by simp [bW]
    | simp

/-! ### Smoothness and the two charts -/

lemma contDiff_Pn {d : ℕ} (N : ℕ) (h : (Fin d → Fin (N + 1)) → ℝ) : ContDiff ℝ ∞ (Pn N h) := by
  unfold Pn W
  refine ContDiff.sum fun m _ => contDiff_const.mul ?_
  exact contDiff_prod fun i _ => (contDiff_bW N (m i)).of_le le_top |>.comp ((contDiff_apply (𝕜 := ℝ) (E := ℝ) i))

lemma contDiff_phiB (B : ℝ) : ContDiff ℝ ∞ (fun p : ℝ × E n => phiB n B p.1 p.2) := by
  rw [contDiff_pi]
  intro i
  refine Fin.cases ?_ (fun l => ?_) i
  · simpa [phiB] using contDiff_fst
  · simp only [phiB, Fin.cons_succ]
    exact (((EuclideanSpace.proj l : E n →L[ℝ] ℝ).contDiff.comp contDiff_snd).add
      contDiff_const).div_const _

lemma contDiff_Htilde {H : ℝ → E n → ℝ} (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2))
    (B : ℝ) : ContDiff ℝ ∞ (Htilde n B H) := by
  unfold Htilde
  have hlin : ContDiff ℝ ∞ (fun ξ : Fin (2 * n + 1) → ℝ =>
      (WithLp.toLp 2 fun l : Fin (2 * n) => 2 * B * ξ l.succ - B : E n)) := by
    refine (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (2 * n) => ℝ)).symm.contDiff.comp ?_
    rw [contDiff_pi]
    intro l
    exact (contDiff_const.mul ((contDiff_apply (𝕜 := ℝ) (E := ℝ) l.succ))).sub contDiff_const
  exact hH.comp (((contDiff_apply (𝕜 := ℝ) (E := ℝ) 0)).prodMk hlin)

lemma H_eq_Htilde (H : ℝ → E n → ℝ) {B : ℝ} (hB : B ≠ 0) (t : ℝ) (z : E n) :
    H t z = Htilde n B H (phiB n B t z) := by
  unfold Htilde phiB
  simp only [Fin.cons_zero, Fin.cons_succ]
  congr 1
  ext l
  simp only [PiLp.toLp_apply]
  field_simp
  ring

lemma phiB_mem_cube {B : ℝ} (hB : 0 < B) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {z : E n}
    (hz : ∀ l, |z l| ≤ B) : phiB n B t z ∈ cube (2 * n + 1) := by
  intro i
  refine Fin.cases ?_ (fun l => ?_) i
  · simpa [phiB] using ht
  · simp only [phiB, Fin.cons_succ, Set.mem_Icc]
    have := abs_le.mp (hz l)
    constructor
    · apply div_nonneg <;> linarith
    · rw [div_le_one (by positivity)]; linarith

lemma phiB_add_single {B : ℝ} (hB : B ≠ 0) (t : ℝ) (z : E n) (l : Fin (2 * n)) (s : ℝ) :
    phiB n B t (z + s • EuclideanSpace.single l 1) =
      Function.update (phiB n B t z) l.succ (phiB n B t z l.succ + s / (2 * B)) := by
  funext i
  refine Fin.cases ?_ (fun l' => ?_) i
  · rw [Function.update_of_ne (Fin.succ_ne_zero l).symm]
    simp [phiB]
  · by_cases h : l' = l
    · subst h
      simp only [Function.update_self, phiB, Fin.cons_succ, PiLp.add_apply, PiLp.smul_apply,
        smul_eq_mul, PiLp.single_apply, ite_true, mul_one]
      field_simp
      ring
    · rw [Function.update_of_ne (fun e => h (Fin.succ_injective _ e))]
      simp [phiB, PiLp.single_apply, h]

/-! ### The compilation datum -/

/-- The compilation bounds (C1)–(C6), before rational grid samples are evaluated. -/
structure CompilationBounds (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) (s : Fin k → E n)
    (H : ℝ → E n → ℝ) where
  /-- (C1) -/
  C₀ : ℝ
  C₀_pos : 0 < C₀
  C₀_lt : C₀ < C
  image : ∀ i, ∀ x ∈ capBall (s i) (c i), ∀ γ : ℝ → E n, γ 0 = x →
    IsIntegralCurveOn γ (Problem.hamVF H) (Icc 0 1) → γ 1 ∈ capBall 0 C₀
  /-- (C2) -/
  Sbox : ℚ
  Sbox_pos : 0 < Sbox
  support : ∀ t (z : E n), (∃ l, (Sbox : ℝ) ≤ |z l|) → H t z = 0
  B : ℕ
  B_gt_dim : 2 * n < B
  B_gt_box : 2 * (Sbox : ℝ) < B
  /-- (C3) -/
  LX : ℝ
  LX_ge : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : E n, 1 + ‖fderiv ℝ (fderiv ℝ (H t)) z‖ ≤ LX
  Cβ : ℝ
  Cβ_ge : ∀ z : E n, 1 + ‖fderiv ℝ (boxCut n B) z‖ ≤ Cβ
  /-- (C4) -/
  bR : ℚ
  bR_pos : 0 < bR
  bR_lt : (bR : ℝ) < (Real.sqrt (C / π) - Real.sqrt (C₀ / π)) / 4
  /-- (C5) -/
  M₀ : ℝ
  M₀_ge : 1 ≤ M₀
  deriv1 : ∀ ξ ∈ cube (2 * n + 1), ∀ j, |cpd (Htilde n B H) j ξ| ≤ M₀
  deriv2 : ∀ ξ ∈ cube (2 * n + 1), ∀ j l, |cpd (cpd (Htilde n B H) j) l ξ| ≤ M₀
  /-- (C6) -/
  δ : ℚ
  δ_pos : 0 < δ
  δ_lt_half : δ < 1 / 2
  δ_lt : (δ : ℝ) < bR * Real.exp (-LX) / 2 / (16 * (1 + Cβ))
  N : ℕ
  N_gt_one : 1 < N
  N_gt_sq : ((2 * n + 1) * M₀ / δ) ^ 2 < N
  N_gt_lin : 4 * M₀ / δ < N

/-- A **compilation datum** (C1)–(C7): the bounds together with certified rational samples. -/
structure CompilationDatum (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) (s : Fin k → E n)
    (H : ℝ → E n → ℝ) extends CompilationBounds n k C c s H where
  /-- (C7) -/
  Hm : (Fin (2 * n + 1) → Fin (N + 1)) → ℚ
  Hm_close : ∀ m, |(Hm m : ℝ) - Htilde n B H (SymplecticPacking.gridPt N m)| < δ / (2 * N + 1)

namespace CompilationDatum

variable {k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n} {H : ℝ → E n → ℝ}

/-- The field tolerance `η = b_R e^{-L_X}/2`. -/
def η (D : CompilationDatum n k C c s H) : ℝ := D.bR * Real.exp (-D.LX) / 2

/-- The compiled polynomial `P ∈ ℚ[t,z]`. -/
def P (D : CompilationDatum n k C c s H) : MvPolynomial (Fin (2 * n + 1)) ℚ :=
  bernsteinMvPoly n D.N D.B D.Hm

/-- The finite Hamiltonian `H_fin = β_B · P`. -/
def Hfin (D : CompilationDatum n k C c s H) : ℝ → E n → ℝ := finiteHam n D.B D.P

end CompilationDatum

/-! ### The polynomial error (Lemma `lem:cpl-poly`) -/

/-- **Lemma `lem:cpl-poly`.** On `[0,1] × [-B,B]^{2n}`: `|P - H| < δ` and every spatial partial
derivative of `P - H` is less than `δ / B` in absolute value. -/
theorem poly_error {H : ℝ → E n → ℝ} (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2))
    {B : ℕ} (hB : 0 < B) {M₀ δ : ℝ} (hM₀ : 0 ≤ M₀) (hδ : 0 < δ)
    (h1 : ∀ ξ ∈ cube (2 * n + 1), ∀ j, |cpd (Htilde n B H) j ξ| ≤ M₀)
    (h2 : ∀ ξ ∈ cube (2 * n + 1), ∀ j l, |cpd (cpd (Htilde n B H) j) l ξ| ≤ M₀)
    {N : ℕ} (hN1 : 1 < N) (hNsq : ((2 * n + 1) * M₀ / δ) ^ 2 < N) (hNlin : 4 * M₀ / δ < N)
    (Hm : (Fin (2 * n + 1) → Fin (N + 1)) → ℚ)
    (hHm : ∀ m, |(Hm m : ℝ) - Htilde n B H (SymplecticPacking.gridPt N m)| < δ / (2 * N + 1))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) {z : E n} (hz : ∀ l, |z l| ≤ B) :
    |evalPoly (bernsteinMvPoly n N B Hm) t z - H t z| < δ ∧
    ∀ l, |fderiv ℝ (fun w => evalPoly (bernsteinMvPoly n N B Hm) t w - H t w) z
      (EuclideanSpace.single l 1)| ≤ δ / B := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hB0 : (B : ℝ) ≠ 0 := hBr.ne'
  set g := Htilde n B H
  have hg := contDiff_Htilde hH (B : ℝ)
  have hgd : Differentiable ℝ g := hg.differentiable (by simp)
  have hgd' : ∀ j, Differentiable ℝ (cpd g j) := fun j => by
    have : ContDiff ℝ ∞ (fun ξ => fderiv ℝ g ξ) := hg.fderiv_right (m := ∞) (by simp)
    exact (this.clm_apply contDiff_const).differentiable (by simp)
  set A : ℝ := δ / (2 * ((M : ℝ) + 1) + 1)
  have hA : ∀ m, |(Hm m : ℝ) - g (SymplecticPacking.gridPt (M + 1) m)| ≤ A := fun m => by
    have := hHm m; push_cast at this; exact this.le
  have hξ := phiB_mem_cube hBr ht hz
  obtain ⟨hval, hder⟩ := cube_error M hgd hgd' hM₀ h1 h2 (fun m => (Hm m : ℝ)) hA hξ
  -- numerical consequences of (C6)
  have hNr : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hq : (2 * (n : ℝ) + 1) * M₀ / δ < Real.sqrt ((M : ℝ) + 1) := by
    apply Real.lt_sqrt_of_sq_lt
    have := hNsq; push_cast at this; linarith
  have hs0 : 0 < Real.sqrt ((M : ℝ) + 1) := Real.sqrt_pos.mpr hNr
  have hT1 : (2 * (n : ℝ) + 1) * M₀ / (2 * Real.sqrt ((M : ℝ) + 1)) < δ / 2 := by
    rw [div_lt_iff₀ hδ] at hq
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hT2 : 2 / ((M : ℝ) + 1) * M₀ ≤ δ / 2 := by
    have := hNlin; push_cast at this
    rw [div_lt_iff₀ hδ] at this
    rw [div_mul_eq_mul_div, div_le_iff₀ hNr]; nlinarith
  have hA3 : A ≤ δ / 3 := by
    simp only [A]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)]
  have hA2 : 2 * ((M : ℝ) + 1) * A < δ := by
    simp only [A]
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [(Nat.cast_nonneg M : (0:ℝ) ≤ M)]
  have hcast : ((2 * n : ℕ) : ℝ) + 1 = 2 * (n : ℝ) + 1 := by push_cast; ring
  refine ⟨?_, fun l => ?_⟩
  · rw [evalPoly_bernsteinMvPoly _ _ hB0, H_eq_Htilde H hB0 t z]
    refine lt_of_le_of_lt hval ?_
    rw [hcast]; linarith
  · obtain ⟨D, hD, hDb⟩ := hder l.succ
    rw [hcast] at hDb
    have hDb' : |D| < 2 * δ := by
      have : M₀ * ((2 * (n : ℝ) + 1) / (2 * Real.sqrt ((M : ℝ) + 1)) + 2 / ((M : ℝ) + 1)) < δ := by
        have e : M₀ * ((2 * (n : ℝ) + 1) / (2 * Real.sqrt ((M : ℝ) + 1)) + 2 / ((M : ℝ) + 1)) =
            (2 * (n : ℝ) + 1) * M₀ / (2 * Real.sqrt ((M : ℝ) + 1)) +
              2 / ((M : ℝ) + 1) * M₀ := by ring
        rw [e]; linarith
      linarith
    -- the line through `z` in direction `e_l`
    set f : E n → ℝ := fun w => evalPoly (bernsteinMvPoly n (M + 1) B Hm) t w - H t w
    have hfd : Differentiable ℝ f := by
      have hP : ContDiff ℝ ∞ (fun w : E n => evalPoly (bernsteinMvPoly n (M + 1) B Hm) t w) := by
        have : (fun w : E n => evalPoly (bernsteinMvPoly n (M + 1) B Hm) t w) =
            fun w => Pn (M + 1) (fun m => (Hm m : ℝ)) (phiB n B t w) :=
          funext fun w => evalPoly_bernsteinMvPoly _ _ hB0 _ t w
        rw [this]
        exact (contDiff_Pn _ _).comp ((contDiff_phiB (n := n) (B : ℝ)).comp
          (contDiff_const.prodMk contDiff_id))
      have hHt : ContDiff ℝ ∞ (H t) := hH.comp (contDiff_const.prodMk contDiff_id)
      exact (hP.sub hHt).differentiable (by simp)
    set e : E n := EuclideanSpace.single l 1
    have hline : HasDerivAt (fun r : ℝ => z + r • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add z
    have h1' : HasDerivAt (fun r : ℝ => f (z + r • e)) (fderiv ℝ f z e) 0 :=
      (hfd z).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    set ξ0 := phiB n B t z
    set Dfun : (Fin (2 * n + 1) → ℝ) → ℝ := fun ξ => Pn (M + 1) (fun m => (Hm m : ℝ)) ξ - g ξ
    have hfeq : (fun r : ℝ => f (z + r • e)) =
        (fun u => Dfun (Function.update ξ0 l.succ u)) ∘ (fun r => ξ0 l.succ + r / (2 * B)) := by
      funext r
      simp only [Function.comp, f, Dfun, ξ0, e]
      rw [evalPoly_bernsteinMvPoly _ _ hB0, H_eq_Htilde H hB0 t, phiB_add_single hB0]
    have hu : HasDerivAt (fun r : ℝ => ξ0 l.succ + r / (2 * B)) (1 / (2 * B)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).div_const (2 * (B : ℝ))).const_add (ξ0 l.succ)
    have h2' : HasDerivAt (fun r : ℝ => f (z + r • e)) (D * (1 / (2 * B))) 0 := by
      rw [hfeq]
      exact hD.comp_of_eq (0 : ℝ) hu (by simp)
    rw [h1'.unique h2', abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * B))]
    calc |D| * (1 / (2 * B)) ≤ 2 * δ * (1 / (2 * B)) :=
          mul_le_mul_of_nonneg_right hDb'.le (by positivity)
      _ = δ / B := by field_simp

/-! ### The global field error (Lemma `lem:cpl-cutoff`) -/

lemma boxCut_mul_eq {H : ℝ → E n → ℝ} {Sb : ℝ} (hS : ∀ t (z : E n), (∃ l, Sb ≤ |z l|) → H t z = 0)
    {B : ℝ} (hB : 0 < B) (hSB : 2 * Sb < B) (t : ℝ) (z : E n) :
    boxCut n B z * H t z = H t z := by
  by_cases h : ∀ l, |z l| ≤ B / 2
  · rw [boxCut_eq_one hB h, one_mul]
  · push_neg at h
    obtain ⟨l, hl⟩ := h
    rw [hS t z ⟨l, by linarith⟩, mul_zero]

/-- **Lemma `lem:cpl-cutoff`.** For `t ∈ [0,1]` and every `z`,
`‖X_{H_fin}(t,z) - X_H(t,z)‖ ≤ δ C_β < 2δ(1 + C_β) < η/8`. -/
theorem field_error {k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n} {H : ℝ → E n → ℝ}
    (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2)) (D : CompilationDatum n k C c s H)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (z : E n) :
    ‖Problem.hamVF D.Hfin t z - Problem.hamVF H t z‖ ≤ D.δ * D.Cβ := by
  have hBn : 0 < D.B := by have := D.B_gt_dim; omega
  have hBr : (0 : ℝ) < D.B := by exact_mod_cast hBn
  have hδ : (0 : ℝ) < D.δ := by exact_mod_cast D.δ_pos
  have hS0 : (0 : ℝ) < D.Sbox := by exact_mod_cast D.Sbox_pos
  set Pt : E n → ℝ := fun w => evalPoly D.P t w
  have hβd : Differentiable ℝ (boxCut n D.B) := (contDiff_boxCut _).differentiable (by simp)
  have hPt : Differentiable ℝ Pt := by
    have : Pt = fun w => Pn D.N (fun m => (D.Hm m : ℝ)) (phiB n D.B t w) :=
      funext fun w => evalPoly_bernsteinMvPoly _ _ hBr.ne' _ t w
    rw [this]
    exact ((contDiff_Pn _ _).comp ((contDiff_phiB (n := n) (D.B : ℝ)).comp
      (contDiff_const.prodMk contDiff_id))).differentiable (by simp)
  have hHt : Differentiable ℝ (H t) :=
    (hH.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
  rw [hamVF_eq_gradField, hamVF_eq_gradField, ← gradField_sub, norm_gradField]
  have hfin : D.Hfin t = fun w => boxCut n D.B w * Pt w := rfl
  have hHeq : H t = fun w => boxCut n D.B w * H t w :=
    funext fun w => (boxCut_mul_eq D.support hBr D.B_gt_box t w).symm
  have dfin : fderiv ℝ (D.Hfin t) z = boxCut n D.B z • fderiv ℝ Pt z + Pt z • fderiv ℝ (boxCut n D.B) z := by
    rw [hfin]; exact ((hβd z).hasFDerivAt.mul (hPt z).hasFDerivAt).fderiv
  have dH : fderiv ℝ (H t) z = boxCut n D.B z • fderiv ℝ (H t) z + H t z • fderiv ℝ (boxCut n D.B) z := by
    conv_lhs => rw [hHeq]
    exact ((hβd z).hasFDerivAt.mul (hHt z).hasFDerivAt).fderiv
  have hdiff : fderiv ℝ (D.Hfin t) z - fderiv ℝ (H t) z =
      boxCut n D.B z • fderiv ℝ (fun w => Pt w - H t w) z + (Pt z - H t z) • fderiv ℝ (boxCut n D.B) z := by
    rw [dfin, fderiv_fun_sub (hPt z) (hHt z)]
    conv_lhs => rw [dH]
    rw [smul_sub, sub_smul]; abel
  rw [hdiff]
  have hCβ := D.Cβ_ge z
  by_cases hz : ∀ l, |z l| ≤ D.B
  · obtain ⟨hv, hd⟩ := poly_error hH hBn (by linarith [D.M₀_ge]) hδ D.deriv1 D.deriv2 D.N_gt_one
      D.N_gt_sq D.N_gt_lin D.Hm D.Hm_close ht hz
    have hgrad : ‖fderiv ℝ (fun w => Pt w - H t w) z‖ ≤ D.δ := by
      refine (opNorm_le_sum_abs _).trans ?_
      calc ∑ l, |fderiv ℝ (fun w => Pt w - H t w) z (EuclideanSpace.single l 1)|
          ≤ ∑ _l : Fin (2 * n), (D.δ : ℝ) / D.B := sum_le_sum fun l _ => hd l
        _ = (2 * n : ℝ) * (D.δ / D.B) := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
        _ ≤ D.δ := by
            have : (2 * n : ℝ) ≤ D.B := by exact_mod_cast D.B_gt_dim.le
            rw [mul_div_assoc', div_le_iff₀ hBr]; nlinarith
    have hβ := boxCut_mem (n := n) D.B z
    calc ‖boxCut n D.B z • fderiv ℝ (fun w => Pt w - H t w) z + (Pt z - H t z) • fderiv ℝ (boxCut n D.B) z‖
        ≤ ‖boxCut n D.B z • fderiv ℝ (fun w => Pt w - H t w) z‖ + ‖(Pt z - H t z) • fderiv ℝ (boxCut n D.B) z‖ :=
          norm_add_le _ _
      _ = |boxCut n D.B z| * ‖fderiv ℝ (fun w => Pt w - H t w) z‖ + |Pt z - H t z| * ‖fderiv ℝ (boxCut n D.B) z‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 1 * D.δ + D.δ * (D.Cβ - 1) := by
          rw [abs_of_nonneg hβ.1]
          have a1 := mul_le_mul hβ.2 hgrad (norm_nonneg _) zero_le_one
          have a2 : |Pt z - H t z| * ‖fderiv ℝ (boxCut n D.B) z‖ ≤ D.δ * (D.Cβ - 1) :=
            mul_le_mul hv.le (by linarith : ‖fderiv ℝ (boxCut n D.B) z‖ ≤ D.Cβ - 1)
            (norm_nonneg _) hδ.le
          linarith
      _ = D.δ * D.Cβ := by ring
  · push_neg at hz
    obtain ⟨l, hl⟩ := hz
    have hl' : 3 * (D.B : ℝ) / 4 < |z l| := by linarith
    rw [show boxCut n D.B z = 0 from boxCut_eq_zero hBr hl'.le, fderiv_boxCut_eq_zero hBr hl']
    simp only [zero_smul, smul_zero, add_zero, norm_zero]
    have : (1 : ℝ) ≤ D.Cβ := by linarith [norm_nonneg (fderiv ℝ (boxCut n D.B) z)]
    exact mul_nonneg hδ.le (by linarith)

/-! ### Lipschitz bound and the flow error (Lemmas `lem:cpl-lipschitz`, `lem:cpl-gronwall`) -/

lemma hamVF_lipschitz {H : ℝ → E n → ℝ} (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2))
    {L : ℝ} {t : ℝ} (hL : ∀ z : E n, 1 + ‖fderiv ℝ (fderiv ℝ (H t)) z‖ ≤ L) (hL0 : 0 ≤ L) :
    LipschitzWith ⟨L, hL0⟩ (Problem.hamVF H t) := by
  have hHt : ContDiff ℝ ∞ (H t) := hH.comp (contDiff_const.prodMk contDiff_id)
  have hd : Differentiable ℝ (fderiv ℝ (H t)) :=
    (hHt.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  refine LipschitzWith.of_dist_le_mul fun y y' => ?_
  rw [dist_eq_norm, dist_eq_norm, hamVF_eq_gradField, hamVF_eq_gradField, ← gradField_sub,
    norm_gradField]
  have := (convex_univ : Convex ℝ (univ : Set (E n))).norm_image_sub_le_of_norm_fderiv_le
    (f := fderiv ℝ (H t)) (C := L) (fun x _ => hd x) (fun x _ => by linarith [hL x])
    (mem_univ y') (mem_univ y)
  exact this

/-- The clamp `t ↦ max 0 (min t 1)` onto `[0,1]`. -/
def clamp01 (t : ℝ) : ℝ := max 0 (min t 1)

lemma clamp01_mem (t : ℝ) : clamp01 t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩

lemma clamp01_of_mem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : clamp01 t = t := by
  simp [clamp01, min_eq_left ht.2, max_eq_right ht.1]

/-- **Lemma `lem:cpl-gronwall`.** Integral curves of `X_{H_fin}` and `X_H` on `[0,1]` from the
same point end at distance `< b_R`. -/
theorem flow_error {k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n} {H : ℝ → E n → ℝ}
    (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2)) (D : CompilationDatum n k C c s H)
    {γ y : ℝ → E n} (hγ : IsIntegralCurveOn γ (Problem.hamVF D.Hfin) (Icc 0 1))
    (hy : IsIntegralCurveOn y (Problem.hamVF H) (Icc 0 1)) (h0 : γ 0 = y 0) :
    dist (γ 1) (y 1) < D.bR := by
  have hLX1 : 1 ≤ D.LX := by
    have := D.LX_ge 0 ⟨le_rfl, zero_le_one⟩ 0
    linarith [norm_nonneg (fderiv ℝ (fderiv ℝ (H 0)) 0)]
  have hδ : (0 : ℝ) < D.δ := by exact_mod_cast D.δ_pos
  have hbR : (0 : ℝ) < D.bR := by exact_mod_cast D.bR_pos
  have hCβ : (1 : ℝ) ≤ D.Cβ := by
    have := D.Cβ_ge 0; linarith [norm_nonneg (fderiv ℝ (boxCut n D.B) (0 : E n))]
  set L : ℝ≥0 := ⟨D.LX, by linarith⟩
  set v : ℝ → E n → E n := fun t => Problem.hamVF H (clamp01 t)
  set w : ℝ → E n → E n := fun t => Problem.hamVF D.Hfin (clamp01 t)
  have hv : ∀ t, LipschitzWith L (v t) := fun t =>
    hamVF_lipschitz hH (D.LX_ge _ (clamp01_mem t)) (by linarith)
  have hη : ∀ t x, dist (w t x) (v t x) ≤ D.η := by
    intro t x
    rw [dist_eq_norm]
    refine (field_error hH D (clamp01_mem t) x).trans ?_
    have h16 := D.δ_lt
    have hpos : 0 < 16 * (1 + D.Cβ) := by linarith
    rw [lt_div_iff₀ hpos] at h16
    unfold CompilationDatum.η
    nlinarith
  have hγ' : IsIntegralCurveOn γ w (Icc 0 1) := fun t ht => by
    simp only [w, clamp01_of_mem ht]; exact hγ t ht
  have hy' : IsIntegralCurveOn y v (Icc 0 1) := fun t ht => by
    simp only [v, clamp01_of_mem ht]; exact hy t ht
  have hfe := SymplecticPacking.flow_error_le (L := L) (ne_of_gt (lt_of_lt_of_le zero_lt_one hLX1) : (D.LX : ℝ) ≠ 0) hv hη hy' hγ' h0
  have hch := SymplecticPacking.eta_choice hLX1 hbR
  unfold CompilationDatum.η at hfe
  exact lt_of_le_of_lt hfe hch

/-! ### The finite output (Theorem `thm:cpl-final`) -/

lemma support_of_coords {f : ℝ → E n → ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hf : ∀ t (z : E n), (∃ l, a ≤ |z l|) → f t z = 0) :
    ∀ t (z : E n), 2 * n * a < ‖z‖ → f t z = 0 := by
  intro t z hz
  apply hf
  by_contra h
  push_neg at h
  have : ‖z‖ ≤ 2 * n * a := by
    refine (norm_le_sum_abs z).trans ?_
    calc ∑ l, |z l| ≤ ∑ _l : Fin (2 * n), a := sum_le_sum fun l _ => (h l).le
      _ = 2 * n * a := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  linarith

/-- **Theorem `thm:eff-finite` / `thm:cpl-final`.** For every compilation datum (C1)–(C7) for a
smooth `H`, the finite Hamiltonian `H_fin = β_B · P` satisfies `PackingSpec n k C c s`. -/
theorem finite_spec {k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n} {H : ℝ → E n → ℝ}
    (hH : ContDiff ℝ ∞ (fun p : ℝ × E n => H p.1 p.2)) (D : CompilationDatum n k C c s H) :
    PackingSpec n k C c s D.Hfin := by
  have hBn : 0 < D.B := by have := D.B_gt_dim; omega
  have hBr : (0 : ℝ) < D.B := by exact_mod_cast hBn
  have hS0 : (0 : ℝ) < D.Sbox := by exact_mod_cast D.Sbox_pos
  -- smoothness
  have hsm : ContDiff ℝ ∞ (fun p : ℝ × E n => D.Hfin p.1 p.2) := by
    have hP : (fun p : ℝ × E n => evalPoly D.P p.1 p.2) =
        fun p => Pn D.N (fun m => (D.Hm m : ℝ)) (phiB n D.B p.1 p.2) :=
      funext fun p => evalPoly_bernsteinMvPoly _ _ hBr.ne' _ p.1 p.2
    have : ContDiff ℝ ∞ (fun p : ℝ × E n => evalPoly D.P p.1 p.2) := by
      rw [hP]; exact (contDiff_Pn _ _).comp (contDiff_phiB _)
    exact ((contDiff_boxCut (n := n) (D.B : ℝ)).comp contDiff_snd).mul this
  -- support
  have hsuppF : ∀ t (z : E n), (∃ l, 3 * (D.B : ℝ) / 4 ≤ |z l|) → D.Hfin t z = 0 := by
    rintro t z ⟨l, hl⟩
    simp [CompilationDatum.Hfin, finiteHam, boxCut_eq_zero hBr hl]
  have hRF := support_of_coords (by positivity) hsuppF
  have hRH := support_of_coords hS0.le D.support
  refine ⟨hsm, ⟨closedBall 0 (2 * n * (3 * (D.B : ℝ) / 4)), isCompact_closedBall _ _,
    fun t y hy => hRF t y (by simpa [mem_closedBall, dist_zero_right] using hy)⟩,
    fun i x _ => exists_integralCurve_global hsm hRF x, ?_⟩
  intro i x hx γ hγ0 hγ
  obtain ⟨y, hy0, hy⟩ := exists_integralCurve_global hH hRH x
  have hyOn : IsIntegralCurveOn y (Problem.hamVF H) (Icc 0 1) := hy.isIntegralCurveOn _
  have hy1 := D.image i x hx y hy0 hyOn
  have hd := flow_error hH D hγ hyOn (by rw [hγ0, hy0])
  -- radial budget
  have hC0 := D.C₀_pos
  have hC := D.C₀_pos.trans D.C₀_lt
  set R0 := Real.sqrt (D.C₀ / π)
  set RC := Real.sqrt (C / π)
  have hy1' : ‖y 1‖ ≤ R0 := by
    apply Real.le_sqrt_of_sq_le
    have : π * ‖y 1 - 0‖ ^ 2 ≤ D.C₀ := hy1
    rw [sub_zero] at this
    rw [le_div_iff₀ Real.pi_pos]; linarith
  have hbR : (0 : ℝ) < D.bR := by exact_mod_cast D.bR_pos
  have hlt := D.bR_lt
  have hγ1 : ‖γ 1‖ < RC := by
    have : ‖γ 1‖ ≤ ‖y 1‖ + dist (γ 1) (y 1) := by
      rw [dist_eq_norm]; exact norm_le_insert' _ _
    linarith
  show π * ‖γ 1 - 0‖ ^ 2 < C
  rw [sub_zero]
  have hRC2 : RC ^ 2 = C / π := Real.sq_sqrt (div_nonneg hC.le Real.pi_pos.le)
  have : ‖γ 1‖ ^ 2 < RC ^ 2 := by
    exact pow_lt_pow_left₀ hγ1 (norm_nonneg _) (by norm_num)
  rw [hRC2, lt_div_iff₀ Real.pi_pos] at this
  linarith

/-- (C1) from a packing specification for the smaller target `B°(C₀)`: the hypothesis `image`
of a compilation datum holds for every `H` with `PackingSpec n k C₀ c s H`. -/
theorem image_of_packingSpec {k : ℕ} {C₀ : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    {H : ℝ → E n → ℝ} (hspec : PackingSpec n k C₀ c s H) :
    ∀ i, ∀ x ∈ capBall (s i) (c i), ∀ γ : ℝ → E n, γ 0 = x →
      IsIntegralCurveOn γ (Problem.hamVF H) (Icc 0 1) → γ 1 ∈ capBall 0 C₀ :=
  fun i x hx γ h0 hγ => by
    have h : π * ‖γ 1 - 0‖ ^ 2 < C₀ := hspec.maps_into i x hx γ h0 hγ
    exact le_of_lt h

end SymplecticPacking.General.Compile
