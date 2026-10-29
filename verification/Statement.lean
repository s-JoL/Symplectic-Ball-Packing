import verification.Problem
import SymplecticPacking.General.Main
import SymplecticPacking.General.MainSupport
import SymplecticPacking.General.MainFlow
import SymplecticPacking.General.MainRadius
import SymplecticPacking.General.Corollaries
import SymplecticPacking.General.Criterion
import SymplecticPacking.General.EpochQuarter
import SymplecticPacking.General.EpochStability
import SymplecticPacking.Explicit
import verification.AxiomCheck

/-!
# The statements

The theorems of the paper about the explicitly defined Hamiltonians
`SymplecticPacking.General.packingHamiltonian`, `SymplecticPacking.General.epochHamiltonian`
and `SymplecticPacking.General.epochHamiltonianQ` (their top-level structure is in
`verification/Algorithm.lean`); every notion in the statements is defined in
`verification/Problem.lean` from Mathlib alone.

* Theorem A (`four_dim_theorem`, with `four_dim_data`) and Proposition B
  (`four_dim_stability`);
* Theorem C (`main_theorem`), with the time support and the support radius of Theorem C(i)
  (`main_time_support`, `main_support_radius`);
* Corollary F (`epoch_theorem`, `epoch_theorem_ten`, `epoch_packing`);
* the time-one flow (`flow_is_integral_curve`, `flow_symplectic_diffeomorphism`,
  `flow_images_disjoint`);
* Corollaries E and G (`equal_balls`, `unequal_cone`) and Corollary D
  (`neighbourhood_criterion`, `flow_neighbourhood_embedding`).

Each theorem is gated by `#assert_publication_axioms`, and the Hamiltonians, the radius
`epochRadiusQ` and the support radius by `#check_explicit`.
-/

open SymplecticPacking.Problem
open scoped ContDiff

/-! ## Theorem A and Proposition B (dimension four) -/

/-- **Theorem A (dimension four).** For every `k ≥ 10` and `ε ∈ (0,1)` let
`R = (k / (1 - ε/4))^{1/4}` (`epochRadiusQ`). The time-one map of the explicit Hamiltonian
`H_{k,ε} = epochHamiltonianQ k ε` carries the closed unit balls centred at
`epochCenter i = (3i, 0, 0, 0)`, `0 ≤ i < k`, into the closed ball `B(R)` about the origin,
with `k / R⁴ = 1 − ε/4 > 1 − ε`; in packing form, into the open ball `{π |y|² < π R²}`. For
these data the construction uses the linear comparison datum (`Branch2.EqualCase`). -/
theorem four_dim_theorem (k : ℕ) (hk : 10 ≤ k) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    EpochSpecR k ε (SymplecticPacking.General.epochRadiusQ k ε)
        (SymplecticPacking.General.epochHamiltonianQ k ε) ∧
      PackingSpec 2 k (Real.pi * SymplecticPacking.General.epochRadiusQ k ε ^ 2)
        (fun _ => Real.pi) (fun i => epochCenter i)
        (SymplecticPacking.General.epochHamiltonianQ k ε) ∧
      (k : ℝ) / SymplecticPacking.General.epochRadiusQ k ε ^ 4 = 1 - ε / 4 ∧
      SymplecticPacking.Branch2.EqualCase k
        (Real.pi * SymplecticPacking.General.epochRadiusQ k ε ^ 2) (fun _ => Real.pi) :=
  ⟨SymplecticPacking.General.epochQ_spec (by omega) hε0 hε1,
    (SymplecticPacking.General.epochQ_packing (by omega) hε0 hε1).1,
    SymplecticPacking.General.epochQ_density (by omega) hε0 hε1,
    SymplecticPacking.General.epochQ_equalCase hk hε0 hε1⟩

/-- **Proposition B (robustness of Theorem A).** The explicit margin `R - R_Q` between the
Epoch radius `R = (k / (1 - ε/2))^{1/4}` and the radius `R_Q = (k / (1 - ε/4))^{1/4}` reached
by `H_{k,ε}` absorbs evaluation errors: any smooth compactly supported `Ĥ` whose field is
`L`-Lipschitz on `[0,1]` and within `η` of `X_{H_{k,ε}}` there, with `η e^L ≤ R - R_Q`, solves
the Epoch problem. -/
theorem four_dim_stability (k : ℕ) (hk : 10 ≤ k) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (Hh : ℝ → E 2 → ℝ) (hsm : ContDiff ℝ ∞ (fun p : ℝ × E 2 => Hh p.1 p.2))
    (hsupp : ∃ K : Set (E 2), IsCompact K ∧ ∀ t, ∀ y ∉ K, Hh t y = 0)
    (L : NNReal) (hL : ∀ t ∈ Set.Icc (0 : ℝ) 1, LipschitzWith L (hamVF Hh t))
    (η : ℝ) (hη : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y,
      ‖hamVF Hh t y - hamVF (SymplecticPacking.General.epochHamiltonianQ k ε) t y‖ ≤ η)
    (hsmall : η * Real.exp L ≤
      SymplecticPacking.General.epochRadius k ε - SymplecticPacking.General.epochRadiusQ k ε) :
    EpochSpecR k ε (SymplecticPacking.General.epochRadius k ε) Hh ∧
      SymplecticPacking.General.epochRadiusQ k ε < SymplecticPacking.General.epochRadius k ε :=
  ⟨SymplecticPacking.General.epoch_stability hk hε0 hε1 Hh hsm hsupp L hL η hη hsmall,
    SymplecticPacking.General.epochRadiusQ_lt_epochRadius (by omega) hε0 hε1⟩

/-- The data of Theorem A are admissible with disjoint source balls, so the general theorems
`main_time_support`, `main_support_radius` and `flow_images_disjoint` apply to
`H_{k,ε} = epochHamiltonianQ k ε`, which is `packingHamiltonian` for these data by definition
(checked by `rfl` in `Algorithm.lean`). -/
theorem four_dim_data (k : ℕ) (hk : 10 ≤ k) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    Admissible 2 k (Real.pi * SymplecticPacking.General.epochRadiusQ k ε ^ 2) (fun _ => Real.pi) ∧
      BallsDisjoint 2 k (fun _ => Real.pi) (fun i => epochCenter i) :=
  ⟨SymplecticPacking.General.epoch_admissible (ε := ε / 2) (by omega) (by linarith) (by linarith),
    SymplecticPacking.General.epoch_disjoint k⟩

/-! ## Theorem C -/

/-- **Theorem C.** Let `n ≥ 2`, `k ≥ 1`, `C > 0` and capacities `c_i > 0` be admissible
(`Σ c_iⁿ < Cⁿ`; `3c_i < C` if `n = 2`; `c_i + c_j < C` for `i ≠ j` if `n ≥ 3`), and let the
closed balls `s_i + B(c_i)` in `ℝ^{2n}` be pairwise disjoint. Then the time-1 flow of the
explicit Hamiltonian `packingHamiltonian n k C c s` carries every `s_i + B(c_i)` into the open
ball `{π|y|² < C}`. -/
theorem main_theorem (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) (s : Fin k → E n)
    (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) :
    PackingSpec n k C c s (SymplecticPacking.General.packingHamiltonian n k C c s) :=
  SymplecticPacking.General.packing_main hA hs

/-- The Hamiltonian also vanishes for all times outside `(0,1)`, as in Theorem C(i). -/
theorem main_time_support (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) (s : Fin k → E n)
    (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) (t : ℝ)
    (ht : t ≤ 0 ∨ 1 ≤ t) (y : E n) :
    SymplecticPacking.General.packingHamiltonian n k C c s t y = 0 :=
  SymplecticPacking.General.packingHamiltonian_eq_zero_of_time hA hs ht y

/-- The explicit compact set of Theorem C(i): the Hamiltonian vanishes outside the closed ball
of the explicit radius `packingSupportRadius` (checked by `#check_explicit`), for all times. -/
theorem main_support_radius (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) (s : Fin k → E n)
    (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) (t : ℝ) (y : E n)
    (hy : SymplecticPacking.General.packingSupportRadius n k C c s < ‖y‖) :
    SymplecticPacking.General.packingHamiltonian n k C c s t y = 0 :=
  SymplecticPacking.General.packingHamiltonian_support_radius hA hs t y
    (by simpa [Metric.mem_closedBall, dist_zero_right] using hy)

/-- **Corollary F (Epoch data).** For `k ≥ 9` and `0 < ε < 1`, the time-1 flow of the explicit
Hamiltonian `epochHamiltonian k ε` carries the `k` closed unit balls centred at
`epochCenter i = (3i, 0, 0, 0)`, `0 ≤ i < k` (Epoch's `s_{i+1}`), into the closed ball `B(R)`
centred at the origin, `R = epochRadius k ε = (k / (1 - ε/2))^{1/4}`, and `k / R⁴ > 1 - ε`. -/
theorem epoch_theorem (k : ℕ) (hk : 9 ≤ k) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    EpochSpecR k ε (SymplecticPacking.General.epochRadius k ε)
      (SymplecticPacking.General.epochHamiltonian k ε) :=
  SymplecticPacking.General.epoch_general k hk ε hε0 hε1

/-- **Epoch's problem as stated** (`k ≥ 10`): a special case of `epoch_theorem`. -/
theorem epoch_theorem_ten (k : ℕ) (hk : 10 ≤ k) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    EpochSpecR k ε (SymplecticPacking.General.epochRadius k ε)
      (SymplecticPacking.General.epochHamiltonian k ε) :=
  epoch_theorem k (by omega) ε hε0 hε1

/-- **Corollary F, full form.** The Epoch Hamiltonian satisfies the packing specification
of Definition 1.1 for `C = π R²`, unit capacities `π` and centres
`epochCenter i = (3i, 0, 0, 0)`, `0 ≤ i < k`: the closed unit balls are carried into the
*open* ball `{π |y|² < π R²}`, and `k / R⁴ = 1 - ε/2` exactly. `epoch_theorem` is the weaker
closed-ball form of the problem statement. -/
theorem epoch_packing (k : ℕ) (hk : 9 ≤ k) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) :
    PackingSpec 2 k (Real.pi * SymplecticPacking.General.epochRadius k ε ^ 2)
        (fun _ => Real.pi) (fun i => epochCenter i)
        (SymplecticPacking.General.epochHamiltonian k ε) ∧
      (k : ℝ) / SymplecticPacking.General.epochRadius k ε ^ 4 = 1 - ε / 2 := by
  refine ⟨SymplecticPacking.General.packing_main
    (SymplecticPacking.General.epoch_admissible hk hε0 hε1)
    (SymplecticPacking.General.epoch_disjoint k), ?_⟩
  rw [SymplecticPacking.General.epochRadius_pow_four hk hε0 hε1]
  exact (SymplecticPacking.General.epochR4_bounds hk hε0 hε1).2

/-! ## The time-one map

`packingFlow n k C c s t x` is the flow of `hamVF (packingHamiltonian n k C c s)`. Its orbits
are integral curves in the sense of `Problem.lean`, and each time-`t` map is a smooth
symplectic diffeomorphism; in particular the images of the source balls are disjoint. -/

theorem flow_is_integral_curve (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) (s : Fin k → E n)
    (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) (x : E n) :
    SymplecticPacking.General.packingFlow n k C c s 0 x = x ∧
    ∀ t, HasDerivAt (fun τ => SymplecticPacking.General.packingFlow n k C c s τ x)
      (hamVF (SymplecticPacking.General.packingHamiltonian n k C c s) t
        (SymplecticPacking.General.packingFlow n k C c s t x)) t :=
  SymplecticPacking.General.packingFlow_integral hA hs x

theorem flow_symplectic_diffeomorphism (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) (s : Fin k → E n)
    (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) (t : ℝ) :
    ∃ Φ : E n ≃ₜ E n, ⇑Φ = SymplecticPacking.General.packingFlow n k C c s t ∧
      ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Φ.symm ∧
      ∀ x v w, omega0 (fderiv ℝ Φ x v) (fderiv ℝ Φ x w) = omega0 v w :=
  SymplecticPacking.General.packingFlow_diffeomorphism hA hs t

theorem flow_images_disjoint (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) (s : Fin k → E n)
    (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) (i j : Fin k) (hij : i ≠ j) :
    Disjoint (SymplecticPacking.General.packingFlow n k C c s 1 '' capBall (s i) (c i))
      (SymplecticPacking.General.packingFlow n k C c s 1 '' capBall (s j) (c j)) :=
  SymplecticPacking.General.packingFlow_disjoint hA hs 1 i j hij

/-! ## Corollaries E and G (equal balls; the four-dimensional cone) -/

/-- **Corollary E.** Equal balls, `k ≥ 2ⁿ` (`n ≥ 3`) or `k ≥ 9` (`n = 2`), filling more than
`1 - ε` of the target volume. -/
theorem equal_balls (n k : ℕ) (C c ε : ℝ) (s : Fin k → E n)
    (hn : 2 ≤ n) (hc : 0 < c) (hC : 0 < C) (hε : ε < 1)
    (hk : if n = 2 then 9 ≤ k else 2 ^ n ≤ k) (hvol : (k : ℝ) * c ^ n < C ^ n)
    (hupper : C ^ n < (k : ℝ) * c ^ n / (1 - ε)) (hs : BallsDisjoint n k (fun _ => c) s) :
    PackingSpec n k C (fun _ => c) s
        (SymplecticPacking.General.packingHamiltonian n k C (fun _ => c) s) ∧
      1 - ε < (k : ℝ) * c ^ n / C ^ n :=
  SymplecticPacking.General.equal_packing hn hc hC hε hk hvol hupper hs

/-- **Corollary G.** Unequal balls in dimension four with `c_i ≤ (Σ c_j²)^{1/2} / 3`, moved
into the ball of capacity `C_ε = (Σ c_j² / (1 - ε/2))^{1/2}`. -/
theorem unequal_cone (k : ℕ) (c : Fin k → ℝ) (s : Fin k → E 2) (ε : ℝ)
    (hk : 1 ≤ k) (hc : ∀ i, 0 < c i) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hcone : ∀ i, c i ≤ Real.sqrt (∑ j, c j ^ 2) / 3) (hs : BallsDisjoint 2 k c s) :
    let Cε := Real.sqrt ((∑ i, c i ^ 2) / (1 - ε / 2))
    PackingSpec 2 k Cε c s (SymplecticPacking.General.packingHamiltonian 2 k Cε c s) ∧
      (∑ i, c i ^ 2) / Cε ^ 2 = 1 - ε / 2 :=
  SymplecticPacking.General.unequal_cone_packing hk hc hε0 hε1 hcone hs

/-! ## Corollary D (dimension `2n ≥ 6`)

A symplectic embedding of a neighbourhood of the source balls into the open target exists
iff the volume and two-ball inequalities hold; when they do, the time-one map above is one. -/

theorem neighbourhood_criterion (n k : ℕ) (hn : 3 ≤ n) (hk : 1 ≤ k) (C : ℝ) (c : Fin k → ℝ)
    (s : Fin k → E n) (hC : 0 < C) (hc : ∀ i, 0 < c i) (hs : BallsDisjoint n k c s) :
    (∃ (U : Set (E n)) (F : E n → E n), IsOpen U ∧ ContDiffOn ℝ ∞ F U ∧
        Topology.IsEmbedding (fun x : U => F x) ∧
        (∀ x ∈ U, ∀ v w, omega0 (fderiv ℝ F x v) (fderiv ℝ F x w) = omega0 v w) ∧
        (∀ i, capBall (s i) (c i) ⊆ U) ∧ Set.MapsTo F U (capBallOpen 0 C)) ↔
      (∑ i, c i ^ n) < C ^ n ∧ ∀ i j, i ≠ j → c i + c j < C :=
  SymplecticPacking.General.symplectic_neighbourhood_criterion hn hk hC hc hs

/-- The time-one map is a symplectic embedding of the open neighbourhood
`U = (φ¹)⁻¹(B°(C))` of the source balls into the open target: the last sentence of
Corollary D, in every dimension. -/
theorem flow_neighbourhood_embedding (n k : ℕ) (C : ℝ) (c : Fin k → ℝ) (s : Fin k → E n)
    (hA : Admissible n k C c) (hs : BallsDisjoint n k c s) :
    let F := SymplecticPacking.General.packingFlow n k C c s 1
    ∃ U : Set (E n), IsOpen U ∧ ContDiffOn ℝ ∞ F U ∧
      Topology.IsEmbedding (fun x : U => F x) ∧
      (∀ x ∈ U, ∀ v w, omega0 (fderiv ℝ F x v) (fderiv ℝ F x w) = omega0 v w) ∧
      (∀ i, capBall (s i) (c i) ⊆ U) ∧ Set.MapsTo F U (capBallOpen 0 C) := by
  intro F
  obtain ⟨Φ, hΦ, hsm, -, hsym⟩ := flow_symplectic_diffeomorphism n k C c s hA hs 1
  have hF : F = Φ := hΦ.symm
  have hopen : IsOpen (capBallOpen (0 : E n) C) :=
    isOpen_lt (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2))
      continuous_const
  refine ⟨F ⁻¹' capBallOpen 0 C, ?_, ?_, ?_, ?_, ?_, fun x hx => hx⟩
  · rw [hF]; exact hopen.preimage Φ.continuous
  · rw [hF]; exact hsm.contDiffOn
  · rw [hF]; exact Φ.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  · intro x _ v w; rw [hF]; exact hsym x v w
  · intro i x hx
    obtain ⟨h0, hd⟩ := flow_is_integral_curve n k C c s hA hs x
    exact (main_theorem n k C c s hA hs).maps_into i x hx _ h0
      ((show IsIntegralCurve _ _ from hd).isIntegralCurveOn _)

-- Axiom gates: the build fails if a theorem depends on an axiom other than the three standard ones.
#assert_publication_axioms main_theorem
#assert_publication_axioms four_dim_theorem
#assert_publication_axioms four_dim_stability
#assert_publication_axioms four_dim_data
#assert_publication_axioms main_time_support
#assert_publication_axioms main_support_radius
#assert_publication_axioms epoch_theorem
#assert_publication_axioms epoch_theorem_ten
#assert_publication_axioms epoch_packing
#assert_publication_axioms flow_is_integral_curve
#assert_publication_axioms flow_symplectic_diffeomorphism
#assert_publication_axioms flow_images_disjoint
#assert_publication_axioms equal_balls
#assert_publication_axioms unequal_cone
#assert_publication_axioms neighbourhood_criterion
#assert_publication_axioms flow_neighbourhood_embedding
#check_explicit SymplecticPacking.General.packingHamiltonian
#check_explicit SymplecticPacking.General.epochHamiltonian
#check_explicit SymplecticPacking.General.epochHamiltonianQ
#check_explicit SymplecticPacking.General.epochRadiusQ
#check_explicit SymplecticPacking.General.packingSupportRadius
