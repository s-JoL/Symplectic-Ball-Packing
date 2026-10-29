import SymplecticPacking.Branch2.Planar.Endpoint
import SymplecticPacking.Qhat.Main

/-!
# Realisation of the rearrangement by a planar Hamiltonian isotopy (`thm:cmp-realisation`, m = 1)

From a `PlanarInput` (convex `F` on `[0,h]`, smooth convex majorant `U₀`, error `e`) the planar
construction produces a five-segment path `planarPath D : Qhat.PathData` which is an ordinary
path in the sense of `Qhat.OrdinaryPath`; the generic construction of `Qhat/Flow.lean`,
`Qhat/Normal.lean`, `Qhat/Ham.lean` then gives the compactly supported Hamiltonian disc isotopy
`Qhat.qhat (planarPath D)` with

  `F(π|q̂₁(z)|²) ≤ (R F)(π|z|²) + e`   for `π|z|² ≤ h`   (`planarPath_comparison`).

Construction (files in this directory):
1. `Well.lean`, `UVWells.lean`: the potentials `U` (on `(0,h)`, critical point `p*`) and `V`
   (on `(-1/2,1/2)`) made exactly quadratic near their minima (tolerance `δ = e/64`), and their
   signed Morse inverses `X_U`, `X_V`;
2. `MorsePair.lean`, `Endpoint.lean`: the Morse pair `X = X_U + ζ`, `Y = X_V + ζ`, the
   rotation/area-normalised inner map `f = F_mor ∘ T⁻¹ ∘ D` and the endpoint `Φ = C ∘ f`, with
   `F(p(Φ(z))) < R F(π|z|²) + e` for `π|z|² ≤ h - 4η` (estimate (F) of `Potential.lean`);
3. `Alexander.lean`: the Alexander family `q_σ = Φ(0) + ∫₀¹ DΦ(tσz) z dt` from `Φ(0) + DΦ(0)` to
   `Φ`;
4. `FiveGeneric.lean`: the five segments (shrink, translate, linear deformation, Alexander
   family, expansion) with `e_q = 2η`, `p† = h - 5η`.
On `{π|z|² > h - 8η}` the estimate follows from `q̂₁(D̄(h)) = D̄(h)` and
`max F ≤ R F(I) + L(h - I)`.
-/

noncomputable section

namespace SymplecticPacking.Branch2.Planar

open Set
open scoped Real

namespace PlanarInput

variable (D : PlanarInput)

/-- **The five-segment path** of the planar realisation: the generic five-segment path of the
Alexander family of the endpoint map, with source-order parameter `e_q = 2η`. -/
def planarPath (D : PlanarInput) : Qhat.PathData := D.alexInput.toFam.pathData (2 * D.eta)

variable {D}

theorem planarPath_h : D.planarPath.h = D.h := rfl

/-- `planarPath D` is an ordinary path (`lem:pln-five-segment` for the general potential pair). -/
theorem Hyp.planarPath_ordinary (hD : D.Hyp) : Qhat.OrdinaryPath D.planarPath :=
  FamData.ordinary (AlexInput.toFam_hyp (alex_hyp hD)) (by linarith [hD.eta_pos])
    (by show 4 * (2 * D.eta) < D.h; linarith [hD.eta_le, hD.h_pos])
    (by show D.h - 15 * (2 * D.eta) / 4 < D.h - 5 * D.eta; linarith [hD.eta_pos])

lemma planarPath_path_one (hD : D.Hyp) (z : ℂ) : D.planarPath.path 1 z = D.endMap z := by
  show D.alexInput.toFam.ordPath 1 z = _
  rw [FamData.ordPath_of_one_le (AlexInput.toFam_hyp (alex_hyp hD)) le_rfl]
  exact AlexInput.toFam_q_one (alex_hyp hD) z

/-- `max(F(0), F(h)) ≤ R F(I) + L(h - I)` for `I ∈ [0, h]`. -/
lemma max_le_rearr (hD : D.Hyp) {I : ℝ} (hI : I ∈ Icc 0 D.h) :
    max (D.F 0) (D.F D.h) ≤ Cmp.rearr D.h D.F I + D.L * (D.h - I) := by
  have hh := hD.h_pos
  have hL := hD.L_nonneg
  obtain ⟨a, ha, hRa⟩ := Cmp.rearr_attained hD.F_cont hI
  have ha1 : a ∈ Icc 0 D.h := ⟨ha.1, by linarith [ha.2, hI.1]⟩
  have ha2 : a + I ∈ Icc 0 D.h := ⟨by linarith [ha.1, hI.1], by linarith [ha.2]⟩
  have l1 := hD.F_lip 0 ⟨le_rfl, hh.le⟩ a ha1
  have l2 := hD.F_lip D.h ⟨hh.le, le_rfl⟩ (a + I) ha2
  rw [zero_sub, abs_neg, abs_of_nonneg ha.1] at l1
  rw [abs_of_nonneg (by linarith [ha.2] : 0 ≤ D.h - (a + I))] at l2
  have m1 := le_max_left (D.F a) (D.F (a + I))
  have m2 := le_max_right (D.F a) (D.F (a + I))
  have e1 : D.L * a ≤ D.L * (D.h - I) := mul_le_mul_of_nonneg_left (by linarith [ha.2]) hL
  have e2 : D.L * (D.h - (a + I)) ≤ D.L * (D.h - I) :=
    mul_le_mul_of_nonneg_left (by linarith [ha.1]) hL
  rw [hRa]
  exact max_le (by linarith [(abs_le.mp l1).2]) (by linarith [(abs_le.mp l2).2])

/-- **`thm:cmp-realisation` (m = 1, endpoint estimate on the whole closed disc).** -/
theorem Hyp.planarPath_comparison (hD : D.Hyp) {z : ℂ} (hz : π * ‖z‖ ^ 2 ≤ D.h) :
    D.F (π * ‖Qhat.qhat D.planarPath 1 z‖ ^ 2) ≤ Cmp.rearr D.h D.F (π * ‖z‖ ^ 2) + D.e := by
  have hO := hD.planarPath_ordinary
  have hη := hD.eta_pos
  have hηh := hD.eta_le
  have hh := hD.h_pos
  have he := hD.e_pos
  rcases le_or_gt (π * ‖z‖ ^ 2) (D.h - 8 * D.eta) with h1 | h1
  · have hq : Qhat.qhat D.planarPath 1 z = D.planarPath.path 1 z :=
      (Qhat.qhat_interface hO).2.2.2.2.2.2.2.2.2.2.2.2 z
        (by show π * ‖z‖ ^ 2 ≤ D.h - 4 * (2 * D.eta); linarith)
    have hz' : π * ‖z‖ ^ 2 ≤ D.h - 4 * D.eta := by linarith
    rw [hq, planarPath_path_one hD, endMap_moment hD hz']
    exact (inner_comparison hD hz').2.2.2.le
  · have hmem : Qhat.qhat D.planarPath 1 z ∈ Qhat.closedAreaDisk D.planarPath.h := by
      have := Qhat.qhat_disk hO (P := D.planarPath.h) hO.Psupp_lt_h.le 1
      rw [← this]; exact ⟨z, hz, rfl⟩
    have hP : π * ‖Qhat.qhat D.planarPath 1 z‖ ^ 2 ∈ Icc 0 D.h := ⟨by positivity, hmem⟩
    have hF1 := hD.F_convex.le_max_of_mem_Icc ⟨le_rfl, hh.le⟩ ⟨hh.le, le_rfl⟩ hP
    have hF2 := max_le_rearr hD (I := π * ‖z‖ ^ 2) ⟨by positivity, hz⟩
    have hL := hD.L_nonneg
    have hLη := hD.L_mul_eta
    have : D.L * (D.h - π * ‖z‖ ^ 2) ≤ D.L * (8 * D.eta) :=
      mul_le_mul_of_nonneg_left (by linarith) hL
    linarith

end PlanarInput

end SymplecticPacking.Branch2.Planar
