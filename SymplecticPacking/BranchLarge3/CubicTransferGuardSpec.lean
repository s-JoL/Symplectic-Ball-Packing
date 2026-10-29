import SymplecticPacking.BranchLarge3.CubicTransferData

/-!
# Geometric transfer conditions from the cubic guards

The finite cubic guards imply the geometric transfer conditions.
-/

noncomputable section
namespace SymplecticPacking.BranchLarge3.RawTransfer
open Set Function Manifold
open HighDim.ToricPackingStages
open OAI.PackingSufficiencySupport
open OAI.PackingSufficiencySupport.Hamiltonian
open OAI.PackingSufficiencySupport.CubicModel
open OAI.PackingSufficiencySupport.FiniteMoment.Radial
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit
open scoped ContDiff Manifold Topology

theorem guards_cut_eq_one (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace)
    {p : ℝ × CubicPhysicalSpace} (hp : ∀ i,0<guards A B D S L K p i) :
    cutoff A B D S L K p=1 := by
  have h0 := hp 0
  have h1 := hp 1
  have h2 := hp 2
  change 0<4*gramSum (atlas K) physicalBasis (primitiveAmbient A B D S L K) p/
      gramLevel (atlas K) physicalBasis (primitiveAmbient A B D S L K) K-2 at h0
  change 0<1-p.1^2 at h1
  change 0<2*(fibreRadius fibreBasis K+1-UMoser.qn fibreBasis p.2.2)-1 at h2
  unfold cutoff transferCut
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith)]
  norm_num

theorem guards_source (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace)
    {p : ℝ × CubicPhysicalSpace} (hp : ∀ i,0<guards A B D S L K p i) :
    p.2∈sourceDomain A B D S L K := by
  have h3 := hp 3
  have h4 := hp 4
  have h5 := hp 5
  have h6 := hp 6
  change 0<A-(squaredRadii (physicalDiskCoordinates L p.2.2)).1-CubicBridge.delta A B L K at h3
  change 0<B-(squaredRadii (physicalDiskCoordinates L p.2.2)).1-
    (squaredRadii (physicalDiskCoordinates L p.2.2)).2-CubicBridge.delta A B L K at h4
  change 0<CubicFamily.R1 (compactBase A B D S L K) (compactFibre A B D S L K)-
    CubicFamily.nsq (inclusion (bridgeMap A B D S L K p.2).1,(bridgeMap A B D S L K p.2).2.2) at h5
  change 0<CubicFamily.gsq (inclusion (bridgeMap A B D S L K p.2).1)-
    CubicFamily.mPar (compactBase A B D S L K) at h6
  exact ⟨by change CubicBridge.delta A B L K < min _ _; exact lt_min (by linarith) (by linarith),
    ⟨by linarith,by linarith⟩⟩

theorem guards_target (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace)
    {p : ℝ × CubicPhysicalSpace} (hp : ∀ i,0<guards A B D S L K p i) :
    familyTarget A B D S L K p∈cubicAffineDomain := by
  have h6 : 0<Complex.normSq (familyTarget A B D S L K p).1.1 := hp 7
  have h7 : 0<Complex.normSq (familyTarget A B D S L K p).1.2 := hp 8
  exact ⟨fun hz => by simp only [hz,Complex.normSq_zero] at h6; exact lt_irrefl 0 h6,
    fun hz => by simp only [hz,Complex.normSq_zero] at h7; exact lt_irrefl 0 h7⟩

theorem guards_gram_pos (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace)
    (hμ : 0<gramLevel (atlas K) physicalBasis (primitiveAmbient A B D S L K) K)
    {p : ℝ × CubicPhysicalSpace} (hp : ∀ i,0<guards A B D S L K p i) :
    0<gramSum (atlas K) physicalBasis (primitiveAmbient A B D S L K) p := by
  have h0 := hp 0
  change 0<4*gramSum (atlas K) physicalBasis (primitiveAmbient A B D S L K) p/
      gramLevel (atlas K) physicalBasis (primitiveAmbient A B D S L K) K-2 at h0
  have hd : 0<4*gramSum (atlas K) physicalBasis (primitiveAmbient A B D S L K) p/
      gramLevel (atlas K) physicalBasis (primitiveAmbient A B D S L K) K := by linarith
  have := (div_pos_iff_of_pos_right hμ).mp hd
  linarith

theorem guards_initial_pos (A B D S : ℕ) (L : ℝ) {K : Set CubicPhysicalSpace}
    (hK : IsCompact K)
    (hg : Continuous (gramSum (atlas K) physicalBasis (primitiveAmbient A B D S L K)))
    (hμ : 0<gramLevel (atlas K) physicalBasis (primitiveAmbient A B D S L K) K)
    (hsource : K⊆sourceDomain A B D S L K)
    (htarget : MapsTo (fun x => familyTarget A B D S L K (0,x)) K cubicAffineDomain)
    {x : CubicPhysicalSpace} (hx : x∈K) : ∀ i,0<guards A B D S L K (0,x) i := by
  have hgle := gramLevel_le (atlas K) physicalBasis hK hg hx
  have hqle := fibreRadius_bound fibreBasis hK hx
  have hfrac : 1≤gramSum (atlas K) physicalBasis (primitiveAmbient A B D S L K) (0,x)/
      gramLevel (atlas K) physicalBasis (primitiveAmbient A B D S L K) K := by
    exact (le_div_iff₀ hμ).2 (by simpa using hgle)
  have hs := hsource hx
  have ht := htarget hx
  have hb : CubicBridge.delta A B L K<
      CubicBridge.margin A B (physicalDiskCoordinates L x.2) := hs.1
  have hbm := lt_min_iff.mp hb
  have hR : CubicFamily.nsq (inclusion (bridgeMap A B D S L K x).1,
      (bridgeMap A B D S L K x).2.2)<
      CubicFamily.R1 (compactBase A B D S L K) (compactFibre A B D S L K) := hs.2.1
  have hgs : CubicFamily.mPar (compactBase A B D S L K)<
      CubicFamily.gsq (inclusion (bridgeMap A B D S L K x).1) := hs.2.2
  intro i
  fin_cases i
  · change 0<4*gramSum (atlas K) physicalBasis (primitiveAmbient A B D S L K) (0,x)/
      gramLevel (atlas K) physicalBasis (primitiveAmbient A B D S L K) K-2
    rw [mul_div_assoc]
    linarith
  · change 0<1-(0:ℝ)^2
    norm_num
  · change 0<2*(fibreRadius fibreBasis K+1-UMoser.qn fibreBasis x.2)-1
    linarith
  · exact sub_pos.mpr hbm.1
  · exact sub_pos.mpr hbm.2
  · exact sub_pos.mpr hR
  · exact sub_pos.mpr hgs
  · exact Complex.normSq_pos.mpr ht.1
  · exact Complex.normSq_pos.mpr ht.2

theorem guards_smooth (A B D S : ℕ) (L : ℝ) (K : Set CubicPhysicalSpace)
    (hgram : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicPhysicalModel)) 𝓘(ℝ,ℝ) ∞
      (gramSum (atlas K) physicalBasis (primitiveAmbient A B D S L K)))
    (hΞ : ContMDiff 𝓘(ℝ,CubicPhysicalModel) 𝓘(ℝ,CubicConeModel) ∞ (bridgeMap A B D S L K))
    (hF : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicPhysicalModel)) 𝓘(ℝ,CubicAmbient) ∞
      (familyTarget A B D S L K)) :
    ∀ i,ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicPhysicalModel)) 𝓘(ℝ,ℝ) ∞
      (fun p => guards A B D S L K p i) := by
  have hv : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicPhysicalModel)) 𝓘(ℝ,PlanePhase (Fin 2)) ∞
      (fun p : ℝ × CubicPhysicalSpace => p.2.2) :=
    (flatProduct_snd_smooth (E:=RealModel) (M:=BaseCurve)).comp contMDiff_snd
  have hq := (UMoser.qn_contDiff fibreBasis).contMDiff.comp hv
  have hradii := squaredRadii_contDiff.contMDiff.comp
    ((physicalDiskCoordinates L).contDiff.contMDiff.comp hv)
  have hr1 := contDiff_fst.contMDiff.comp hradii
  have hr2 := contDiff_snd.contMDiff.comp hradii
  have hb := hΞ.comp (contMDiff_snd :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicPhysicalModel)) 𝓘(ℝ,CubicPhysicalModel) ∞
      (Prod.snd : ℝ × CubicPhysicalSpace → CubicPhysicalSpace))
  have hbase := (flatProduct_fst_smooth (E:=RealModel) (M:=BaseCurve) (V:=DiskPair)).comp hb
  have hdisk := (flatProduct_snd_smooth (E:=RealModel) (M:=BaseCurve) (V:=DiskPair)).comp hb
  have hy : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicPhysicalModel)) 𝓘(ℝ,CubicFamily.Y) ∞
      (fun p : ℝ × CubicPhysicalSpace => (inclusion (bridgeMap A B D S L K p.2).1,
        (bridgeMap A B D S L K p.2).2.2)) :=
    (inclusion_real_contMDiff.comp hbase).prodMk_space (contDiff_snd.contMDiff.comp hdisk)
  have hn := CubicFamily.nsq_contDiff.contMDiff.comp hy
  have hgs := CubicFamily.gsq_contDiff.contMDiff.comp (contDiff_fst.contMDiff.comp hy)
  have hz0 := CubicFamily.normSq_contDiff.contMDiff.comp (contDiff_fst.contMDiff.comp (contDiff_fst.contMDiff.comp hF))
  have hz1 := CubicFamily.normSq_contDiff.contMDiff.comp (contDiff_snd.contMDiff.comp (contDiff_fst.contMDiff.comp hF))
  intro i
  fin_cases i
  · change ContMDiff _ _ ∞ (fun p => 4*gramSum (atlas K) physicalBasis
      (primitiveAmbient A B D S L K) p/gramLevel (atlas K) physicalBasis (primitiveAmbient A B D S L K) K-2)
    exact ((contMDiff_const.mul hgram).div_const _).sub contMDiff_const
  · change ContMDiff _ _ ∞ (fun p : ℝ × CubicPhysicalSpace => 1-p.1^2)
    exact contMDiff_const.sub (contMDiff_fst.pow 2)
  · change ContMDiff _ _ ∞ (fun p : ℝ × CubicPhysicalSpace =>
      2*(fibreRadius fibreBasis K+1-UMoser.qn fibreBasis p.2.2)-1)
    exact (contMDiff_const.mul (contMDiff_const.sub hq)).sub contMDiff_const
  · exact (contMDiff_const.sub hr1).sub contMDiff_const
  · exact ((contMDiff_const.sub hr1).sub hr2).sub contMDiff_const
  · exact contMDiff_const.sub hn
  · exact hgs.sub contMDiff_const
  · exact hz0
  · exact hz1

end SymplecticPacking.BranchLarge3.RawTransfer
