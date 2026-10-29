import SymplecticPacking.Branch2.Model.Data
import SymplecticPacking.Branch2.Model.Cubic.Embed.Assemble

/-!
# The model-stage embeddings for general `CubicData` (`thm:cub-packing`, `prop:rtc-embeddings`)

`fcapGen D i = c2ToE4 ∘ compositeBall d_n h ∘ Ncoord ∘ Φ⁻¹ ∘ 𝒟⁻¹ ∘ E_i` for `D : CubicData`:

* `E_i` — the layer map of ball `i` (`Cubic/Strip/Layer.lean`, `Cubic/Strip/LayerMaps.lean`),
  with the per-ball strip slack `δ_i = D.deltaStrip i`, cap `h_i = D.hi i` and the nonlinear
  layer coefficient `a_i(p) = J(p) + Σ_{j<i} h_j(p)` (multi-angle shear with `a_i'(p)`, which is
  not affine; `lem:hdl-shear`);
* `𝒟⁻¹` — the handle map `DlamInv D 1` with `q̂ = Qhat.qhat D.path` (`Cubic/Handle/Twist.lean`,
  `Cubic/Handle/SecondStage.lean`);
* `Φ⁻¹` — the handle Moser map (`Cubic/Handle/HandleMoser.lean`), with `J = K - H*` nonlinear;
* the return `compositeBall d_n h` and the ball chart depend only on `d_n`, `h` (`Return/*`).

The source of ball `i` is the Euclidean ball `{π‖X‖² < ρ̂_i}` (`srcBallGen D i`), closed part
`{π‖X‖² ≤ ρ̄_i}`. The spec theorems are `Valid.fcapGen_smooth`, `Valid.fcapGen_symplectic`,
`Valid.fcapGen_injective`, `Valid.fcapGen_disjoint`, `Valid.fcapGen_mem_ball`.

The constructions for general data are `Branch2/Model/Cubic/{Bundle,Handle,Strip,Embed}`
(written for `P : VCubic`, i.e. data together with its validity; `Cubic/Base.lean`);
`fcapGen D i` is `Embed.Cubic.fcapV ⟨D, hD⟩ i` when `hD : D.Valid` (and the identity otherwise —
the `if` is a decidability site on a proposition, no choice of a witness). The specification
below is the interface used by `Branch2/Unequal.lean`.
-/

noncomputable section

namespace SymplecticPacking.Branch2

open Set
open scoped Real ContDiff

namespace CubicData

variable (D : CubicData)

/-- The open source ball of ball `i`, `{π‖X‖² < ρ̂_i}`. -/
def srcBallGen (i : ℕ) : Set E4 := {X | π * ‖X‖ ^ 2 < D.rhoHat i}

open Classical in
/-- **The capacity-scale embeddings** `f_i^cap` of the cubic model for general data
(see the module docstring). -/
def fcapGen (D : CubicData) (i : ℕ) : E4 → E4 :=
  if hD : D.Valid then Embed.Cubic.fcapV ⟨D, hD⟩ i else id

lemma fcapGen_eq {D : CubicData} (hD : D.Valid) (i : ℕ) :
    D.fcapGen i = Embed.Cubic.fcapV ⟨D, hD⟩ i := by
  simp [fcapGen, hD]

variable {D}

/-- **`prop:rtc-embeddings` (1), smoothness** (general data). -/
theorem Valid.fcapGen_smooth (hD : D.Valid) {i : ℕ} (h1 : 1 ≤ i) (hk : i ≤ D.k) {X : E4}
    (hX : X ∈ D.srcBallGen i) : ContDiffAt ℝ ∞ (D.fcapGen i) X := by
  rw [fcapGen_eq hD]
  exact Embed.Cubic.fcapV_smooth ⟨D, hD⟩ h1 hk hX

/-- **`prop:rtc-embeddings` (1), symplecticity** (general data). -/
theorem Valid.fcapGen_symplectic (hD : D.Valid) {i : ℕ} (h1 : 1 ≤ i) (hk : i ≤ D.k) {X : E4}
    (hX : X ∈ D.srcBallGen i) : IsSymplecticLinear (fderiv ℝ (D.fcapGen i) X) := by
  rw [fcapGen_eq hD]
  exact Embed.Cubic.fcapV_symplectic ⟨D, hD⟩ h1 hk hX

/-- **`prop:rtc-embeddings` (1), injectivity** on the open source ball (general data). -/
theorem Valid.fcapGen_injective (hD : D.Valid) {i : ℕ} (h1 : 1 ≤ i) (hk : i ≤ D.k) :
    InjOn (D.fcapGen i) (D.srcBallGen i) := by
  rw [fcapGen_eq hD]
  exact Embed.Cubic.fcapV_injective ⟨D, hD⟩ h1 hk

/-- **`prop:rtc-embeddings` (2), disjointness** (general data). -/
theorem Valid.fcapGen_disjoint (hD : D.Valid) {i j : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ D.k)
    (hj1 : 1 ≤ j) (hjk : j ≤ D.k) (hij : i ≠ j) :
    Disjoint (D.fcapGen i '' D.srcBallGen i) (D.fcapGen j '' D.srcBallGen j) := by
  rw [fcapGen_eq hD, fcapGen_eq hD]
  exact Embed.Cubic.fcapV_disjoint ⟨D, hD⟩ hi1 hik hj1 hjk hij

/-- **`prop:rtc-embeddings` (3)**: `π‖f_i^cap‖² < 1` (general data). -/
theorem Valid.fcapGen_mem_ball (hD : D.Valid) {i : ℕ} (h1 : 1 ≤ i) (hk : i ≤ D.k) {X : E4}
    (hX : X ∈ D.srcBallGen i) : π * ‖D.fcapGen i X‖ ^ 2 < 1 := by
  rw [fcapGen_eq hD]
  exact Embed.Cubic.fcapV_mem_ball ⟨D, hD⟩ h1 hk hX

end CubicData

end SymplecticPacking.Branch2
