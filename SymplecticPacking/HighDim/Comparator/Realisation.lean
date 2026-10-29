import SymplecticPacking.HighDim.Comparator.Poly
import SymplecticPacking.HighDim.Comparator.Isotopy
import SymplecticPacking.HighDim.Comparator.RealiseGen
import SymplecticPacking.HighDim.Comparator.RealiseGenSpec

/-!
# Planar realisation of one rearrangement (paper thm:cmp-realisation; supplement S-thm:plc-lift)

For convex piecewise-affine `F` on `Δ`, a coordinate `j` and `e > 0` there is an explicit
generator `Q^{(j)}` whose time-one map `q^{(j)}` preserves `V_Δ`, has outer-face collars, and
satisfies `F(p(q^{(j)}(w))) ≤ (R_j F)(p(w)) + e` on `V_Δ`.
Construction:
1. soft-min inner slice length `ℓ(y) < L_j(y)` on an enlarged parameter box;
2. strictly convex analytic potential: softmax of the pieces + endpoint proper barrier
   `δ(1/x + 1/(ℓ−x))` + even angular wall;
3. joint Morse chart, rotation and area normalisation, uniform energy bound;
4. one five-segment ordinary family, whole-path normalisation, common outer collar;
5. lift to the whole fibre by the cutoff `χ(y)` and `χ ℓ B(y, χ t, z_j/√ℓ)`.
-/

noncomputable section

namespace SymplecticPacking.HighDim

open Set
open OAI.PackingSufficiencySupport.Hamiltonian (planeMoments)
open OAI.PackingSufficiencySupport.MomentPolytope (Moments region planeRegion)

variable {m q : ℕ}

/-- The generator realising `R_j` on `F` up to `e`: the lift
`Q(t,z) = χ(y) S'(t) ℓ(y) B(y, χ(y) S(t), z_j/√ℓ(y))` of the planar generator `B`
(see `Comparator/RealiseGen.lean`). -/
def realiseGen (Δ : Polytope m q) (F : PolyFn m) (j : Fin m) (e : ℝ) :
    ℝ → Fibre m → ℝ :=
  RealiseGen.liftGen Δ F j e

theorem realiseGen_spec {Δ : Polytope m q} (hΔ : Δ.Spec) {F : PolyFn m} (hF : F ≠ [])
    (j : Fin m) {e : ℝ} (he : 0 < e) :
    GenSpec (realiseGen Δ F j e) ∧ PreservesRegion Δ (realiseGen Δ F j e) ∧
      FaceCollar Δ (realiseGen Δ F j e) ∧
      ∀ w ∈ planeRegion Δ.b Δ.ℓ,
        PolyFn.eval F (planeMoments (isoOf (realiseGen Δ F j e) 1 w)) ≤
          rearr Δ j (PolyFn.eval F) (planeMoments w) + e :=
  liftGen_spec hΔ hF j he

end SymplecticPacking.HighDim
