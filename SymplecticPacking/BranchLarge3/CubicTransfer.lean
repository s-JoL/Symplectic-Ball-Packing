import SymplecticPacking.BranchLarge3.CubicBridge
import SymplecticPacking.BranchLarge3.CubicFamily
import SymplecticPacking.BranchLarge3.CubicTransferMap

/-!
# Step S4: explicit transfer from the physical normal model to the cubic ambient form

Explicit version of the OpenAI theorem `CubicModel.exists_actual_cubic_normal_transfer_into`
with target `T = cubicAffineDomain`: for a compact set `K` of the physical space
`BaseCurve × ℂ²` lying over the lower trapezoid on which the physical form is nondegenerate, an
explicit degeneration time `t > 0` and an explicit symplectic embedding `g` of a neighbourhood of
`K` into `cubicAffineDomain` pulling `cubicAmbientForm D S (1/(Lπ)) t` back to the physical form.

* S4a (`bridgeMap`, `bridgeDomain`; file `CubicBridge`): the radial bridge `Ξ` from the physical coordinates to the
  disk coordinates of the cubic cone (OpenAI `exists_compact_physical_radial_bridge`, with the
  coefficient weights `a = coefficientSquares (cubicCoefficients D S ·)`).
* S4b (`famMap`, `famPrim`, `famEps`, `famDomain`; file `CubicFamily`): the exact cubic degeneration family
  `Φ_t`, `Γ_t` on the cone space (OpenAI `exists_actual_cubic_exact_family_with_zero`).
* S45 (`RawTransfer.safeTime`, `RawTransfer.transferMap`): the finite-guard compact transfer.
* S4 (`cubicTime`, `cubicMap`, proved from S4a, S4b, S45).

Paper: supplement `six-return.tex` (cubic degeneration, compact degeneration transfer).
-/

noncomputable section

namespace SymplecticPacking.BranchLarge3

open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.FiniteMoment
open OAI.PackingSufficiencySupport.FiniteMoment.Radial
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology
open Set

theorem baseCurve_sigmaCompact : SigmaCompactSpace BaseCurve := curveSigmaCompact (parameters 0)

attribute [local instance] baseCurve_sigmaCompact

/-! ### S4a, S4b

The radial bridge (`bridgeMap`, `bridgeDomain`, `bridge_spec`) is in
`SymplecticPacking.BranchLarge3.CubicBridge`; the exact cubic degeneration family (`famMap`,
`famPrim`, `famEps`, `famDomain`, `fam_spec`) is in `SymplecticPacking.BranchLarge3.CubicFamily`. -/

/-! ### S4: composition -/

section comp

variable (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace)

/-- The compact base and disk parts of `Ξ '' K`. -/
def cubicKB : Set BaseCurve := Prod.fst '' (bridgeMap A B D S L K '' K)
def cubicKH : Set DiskPair := Prod.snd '' (bridgeMap A B D S L K '' K)

/-- The pulled-back primitive family `Δ_t = Ξ^* Γ_t`. -/
def cubicDelta : ℝ → ManifoldOneForm CubicPhysicalModel CubicPhysicalSpace :=
  manifoldPullbackOneForm
    (famPrim A B D S (1 / (L * Real.pi)) (cubicKB A B D S L K) (cubicKH A B D S L K))
    (bridgeMap A B D S L K)

/-- The family of maps `F(t, x) = Φ(t, Ξ x)`. -/
def cubicF : ℝ × CubicPhysicalSpace → CubicAmbient := fun p =>
  famMap A B D S (1 / (L * Real.pi)) (cubicKB A B D S L K) (cubicKH A B D S L K)
    (p.1, bridgeMap A B D S L K p.2)

/-- The open domain `O = V ∩ Ξ⁻¹ U`. -/
def cubicO : Set CubicPhysicalSpace :=
  bridgeDomain A B D S L K ∩ bridgeMap A B D S L K ⁻¹'
    famDomain A B D S (1 / (L * Real.pi)) (cubicKB A B D S L K) (cubicKH A B D S L K)

/-- The family time bound. -/
def cubicEps : ℝ :=
  famEps A B D S (1 / (L * Real.pi)) (cubicKB A B D S L K) (cubicKH A B D S L K)

/-- The explicit degeneration time. -/
def cubicTime : ℝ :=
  RawTransfer.safeTime A B D S L K

/-- The explicit transfer map. -/
def cubicMap : CubicPhysicalSpace → CubicAmbient :=
  RawTransfer.transferMap A B D S L K

end comp

/-- The exact geometric data of the radial bridge and degeneration family. -/
structure CubicTransferGeometry (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace) : Prop where
  bridge_smooth : ContMDiff 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicConeModel) ∞ (bridgeMap A B D S L K)
  bridge_open : IsOpen (bridgeDomain A B D S L K)
  bridge_contains : K⊆bridgeDomain A B D S L K
  primitive_smooth : SmoothOneFormFamily (cubicDelta A B D S L K)
  initial_exterior : ∀ x∈bridgeDomain A B D S L K,
    manifoldExteriorOneForm (cubicDelta A B D S L K 0) x = cubicPhysicalForm (A:=A) (B:=B) D S L x
  eps_pos : 0<cubicEps A B D S L K
  family_smooth : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicPhysicalModel)) 𝓘(ℝ,CubicAmbient) ∞ (cubicF A B D S L K)
  source_open : IsOpen (cubicO A B D S L K)
  source_contains : K⊆cubicO A B D S L K
  family_embedding : ∀ t∈Ioc (0:ℝ) (cubicEps A B D S L K),
    Topology.IsEmbedding (fun x : cubicO A B D S L K => cubicF A B D S L K (t,x.val))
  family_form : ∀ t∈Ioc (0:ℝ) (cubicEps A B D S L K),∀ x∈cubicO A B D S L K,
    manifoldExteriorOneForm (cubicDelta A B D S L K t) x =
      (cubicAmbientForm (A:=A) (B:=B) D S (1/(L*Real.pi)) t (cubicF A B D S L K (t,x))).bilinearComp
        (manifoldMapDifferential (E:=CubicAmbient) (F:=CubicPhysicalModel) (fun y => cubicF A B D S L K (t,y)) x)
        (manifoldMapDifferential (E:=CubicAmbient) (F:=CubicPhysicalModel) (fun y => cubicF A B D S L K (t,y)) x)
  family_zero : MapsTo (fun x => cubicF A B D S L K (0,x)) K cubicAffineDomain

theorem cubicTransfer_geometry {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    (D S : ℕ) {L : ℝ} (hL : 0<L) {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    (hKd : ∀ p∈K,physicalParameter L (planeMoments p.2)∈Radial.lowerTrapezoid A B) :
    CubicTransferGeometry A B D S L K := by
  have ha : ContMDiff 𝓘(ℝ, RealModel) 𝓘(ℝ, TrapezoidWeight A B → ℝ) ∞
      (fun x : BaseCurve => coefficientSquares (cubicCoefficients (A := A) (B := B) D S x)) :=
    coefficientSquares_contDiff.contMDiff.comp (cubicCoefficients_smooth D S)
  obtain ⟨hΞ, hΞfst, hV, hKV, hVd, hΞemb, hΞeq⟩ := bridge_spec hA hAB D S hL hK
    (fun p hp => (physicalDiskCoordinates_mem hL.le p.2).mpr (hKd p hp))
  set Ξ := bridgeMap A B D S L K with hΞdef
  set V := bridgeDomain A B D S L K with hVdef
  have hIK : IsCompact (Ξ '' K) := hK.image hΞ.continuous
  obtain ⟨hδ, hU, hUK, hΨ, hΨ0, hΓ, hΓ0, hΨemb, hΓform⟩ :=
    fam_spec (A := A) (B := B) (K := cubicKB A B D S L K) (H := cubicKH A B D S L K) D S
      (1 / (L * Real.pi)) (hIK.image continuous_fst) (hIK.image continuous_snd)
  set Ψ := famMap A B D S (1 / (L * Real.pi)) (cubicKB A B D S L K) (cubicKH A B D S L K)
  set Γ := famPrim A B D S (1 / (L * Real.pi)) (cubicKB A B D S L K) (cubicKH A B D S L K)
  set U := famDomain A B D S (1 / (L * Real.pi)) (cubicKB A B D S L K) (cubicKH A B D S L K)
  set δ := famEps A B D S (1 / (L * Real.pi)) (cubicKB A B D S L K) (cubicKH A B D S L K)
  have hKU : MapsTo Ξ K U := by
    intro x hx
    exact hUK ⟨⟨Ξ x, ⟨x, hx, rfl⟩, rfl⟩, ⟨Ξ x, ⟨x, hx, rfl⟩, rfl⟩⟩
  set Δ := cubicDelta A B D S L K with hΔdef
  have hΔ : SmoothOneFormFamily Δ := manifoldPullbackOneForm_smooth hΞ hΓ
  have hΔ0 (x : CubicPhysicalSpace) (hx : x ∈ V) : Δ 0 x =
      (productHorizontalLift (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2))
        (physicalPrimitive (A := A) (B := B) D S (1 / (L * Real.pi)) L ∘ planeMoments) +
        (verticalLiouville : ManifoldOneForm CubicPhysicalModel CubicPhysicalSpace)) x := by
    have h := cubic_radial_primitive hA hAB D S hL hΞ hΞfst
      ((physicalDiskCoordinates_mem hL.le x.2).mp (hVd x hx))
      (by filter_upwards [hV.mem_nhds hx] with y hy; exact hΞeq y hy)
    change manifoldPullbackOneForm Γ Ξ 0 x = _
    simp only [manifoldPullbackOneForm] at h ⊢
    rw [hΓ0]
    exact h
  have hΔext (x : CubicPhysicalSpace) (hx : x ∈ V) :
      manifoldExteriorOneForm (Δ 0) x = cubicPhysicalForm (A := A) (B := B) D S L x := by
    apply coupling_exterior_of_primitive_germ (hΔ.comp (contDiff_const (c := (0 : ℝ))))
    filter_upwards [hV.mem_nhds hx] with y hy
    exact hΔ0 y hy
  set F := cubicF A B D S L K with hFdef
  have hF : ContMDiff ((𝓘(ℝ, ℝ)).prod 𝓘(ℝ, CubicPhysicalModel)) 𝓘(ℝ, CubicAmbient) ∞ F :=
    hΨ.comp (contMDiff_fst.prodMk (hΞ.comp contMDiff_snd))
  set O := cubicO A B D S L K with hOdef
  have hO : IsOpen O := hV.inter (hU.preimage hΞ.continuous)
  have hKO : K ⊆ O := fun x hx => ⟨hKV hx, hKU hx⟩
  have htI {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) δ) : t ∈ Icc (-δ) δ := ⟨by linarith [ht.1], ht.2⟩
  have hFemb (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) δ) : Topology.IsEmbedding (fun x : O => F (t, x.val)) :=
    (hΨemb t (htI ht) (ne_of_gt ht.1)).comp
      (((hΞemb.comp (Topology.IsEmbedding.inclusion inter_subset_left)).codRestrict U)
        (fun x : O => x.property.2))
  have hFform (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) δ) (x : CubicPhysicalSpace) (hx : x ∈ O) :
      manifoldExteriorOneForm (Δ t) x =
        (cubicAmbientForm (A := A) (B := B) D S (1 / (L * Real.pi)) t (F (t, x))).bilinearComp
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicPhysicalModel) (fun y => F (t, y)) x)
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicPhysicalModel) (fun y => F (t, y)) x) := by
    have hs := hΨ.comp (contMDiff_const.prodMk contMDiff_id) (f := fun y : CubicConeSpace => (t, y))
    have he := manifold_pullback_exterior
      (fun c y hy => (hΓ.spatial_smooth t c hy).contDiffWithinAt) hΞ x
    change manifoldExteriorOneForm (Δ t) x =
      (manifoldExteriorOneForm (Γ t) (Ξ x)).bilinearComp
        (manifoldMapDifferential (E := CubicConeModel) (F := CubicPhysicalModel) Ξ x)
        (manifoldMapDifferential (E := CubicConeModel) (F := CubicPhysicalModel) Ξ x) at he
    rw [he, hΓform t (htI ht) (ne_of_gt ht.1) (Ξ x) hx.2]
    have hdiff := manifoldMapDifferential_comp
      (hs.mdifferentiable (by simp) (Ξ x)) (hΞ.mdifferentiable (by simp) x)
    change manifoldMapDifferential (E := CubicAmbient) (F := CubicPhysicalModel)
      (fun y => F (t, y)) x = _ at hdiff
    rw [hdiff]
    rfl
  have hF0 : MapsTo (fun x => F (0, x)) K cubicAffineDomain := by
    intro x _hx
    change Ψ (0, Ξ x) ∈ cubicAffineDomain
    rw [hΨ0]
    exact inclusion_mem_cubicAffineDomain _ _
  exact ⟨hΞ,hV,hKV,hΔ,hΔext,hδ,hF,hO,hKO,hFemb,hFform,hF0⟩

theorem cubicTransfer_spec {A B : ℕ} (hA : 0 < A) (hAB : A ≤ B)
    (D S : ℕ) {L : ℝ} (hL : 0 < L) {K : Set CubicPhysicalSpace} (hK : IsCompact K)
    (hKd : ∀ p ∈ K, physicalParameter L (planeMoments p.2) ∈ Radial.lowerTrapezoid A B)
    (hinv : ∀ p ∈ K, (cubicPhysicalForm (A := A) (B := B) D S L p).IsInvertible) :
    let t := cubicTime A B D S L K
    let g := cubicMap A B D S L K
    0 < t ∧ ∃ W : Set CubicPhysicalSpace,
      IsOpen W ∧ K ⊆ W ∧ ContMDiffOn 𝓘(ℝ, CubicPhysicalModel) 𝓘(ℝ, CubicAmbient) ∞ g W ∧
      Topology.IsEmbedding (fun x : W => g x.val) ∧ MapsTo g W cubicAffineDomain ∧
      ∀ x ∈ W, ∀ v w, cubicAmbientForm (A := A) (B := B) D S (1 / (L * Real.pi)) t (g x)
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicPhysicalModel) g x v)
        (manifoldMapDifferential (E := CubicAmbient) (F := CubicPhysicalModel) g x w) =
        cubicPhysicalForm (A := A) (B := B) D S L x v w := by
  intro t g
  have H := cubicTransfer_geometry hA hAB D S hL hK hKd
  have hsemantic : RawTransfer.semanticPrimitive A B D S L K = cubicDelta A B D S L K :=
    RawTransfer.primitive_semantic_eq hA hAB D S L hK H.bridge_smooth
  have hnondeg : ∀ x∈K,
      (manifoldExteriorOneForm (RawTransfer.semanticPrimitive A B D S L K 0) x).IsInvertible := by
    intro x hx
    rw [hsemantic,H.initial_exterior x (H.bridge_contains hx)]
    exact hinv x hx
  have hform (s : ℝ) (hs : s∈Ioc (0:ℝ) (cubicEps A B D S L K))
      (x : CubicPhysicalSpace) (hx : x∈cubicO A B D S L K) :
      manifoldExteriorOneForm (RawTransfer.semanticPrimitive A B D S L K s) x =
        (cubicAmbientForm (A:=A) (B:=B) D S (1/(L*Real.pi)) s (cubicF A B D S L K (s,x))).bilinearComp
          (manifoldMapDifferential (E:=CubicAmbient) (F:=CubicPhysicalModel) (fun y => cubicF A B D S L K (s,y)) x)
          (manifoldMapDifferential (E:=CubicAmbient) (F:=CubicPhysicalModel) (fun y => cubicF A B D S L K (s,y)) x) := by
    rw [hsemantic]
    exact H.family_form s hs x hx
  obtain ⟨ht,W,hW,hKW,hg,hgemb,hgT,hgform⟩ := RawTransfer.transfer_spec hA hAB D S L hK
    H.bridge_smooth hnondeg H.family_smooth H.source_open H.source_contains H.family_zero H.family_embedding
    (fun s => cubicAmbientForm (A:=A) (B:=B) D S (1/(L*Real.pi)) s) hform
  let V := bridgeDomain A B D S L K
  refine ⟨ht.1,W∩V,hW.inter H.bridge_open,fun x hx => ⟨hKW hx,H.bridge_contains hx⟩,
    hg.mono inter_subset_left,?_,fun x hx => hgT hx.1,?_⟩
  · exact RawTransfer.restrict_embedding (RawTransfer.transferMap A B D S L K)
      (show W∩V⊆W from inter_subset_left) hgemb
  · intro x hx v w
    have he := hgform x hx.1 v w
    rw [hsemantic,H.initial_exterior x hx.2] at he
    exact he

#check_explicit cubicTime
#check_explicit cubicMap

end SymplecticPacking.BranchLarge3
