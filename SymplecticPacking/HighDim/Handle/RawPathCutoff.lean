import SymplecticPacking.HighDim.Handle.RawCovectorRegularity
import SymplecticPacking.HighDim.Handle.RawGram

/-!
# Chart determinants and the Moser path cutoff

Finite native chart determinants and a cutoff for an entire Moser path.
-/

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages.NativePathCutoff
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E M V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [TopologicalSpace M] [T2Space M]
  [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def chartGram (B : RawAmbientBox E M) (b : Module.Basis ι ℝ (Plane × V))
    (a : ℝ → M × V → (E × V) →L[ℝ] ℝ) (p : ℝ × (Plane × V)) : ℝ :=
  RawGram.gram b (B.fullForm (a p.1) p.2)^2

/-- The chart determinant is multiplied by a bump whose closed support is strictly inside
that same chart. This formula is a genuine zero extension. -/

theorem chartGram_semantic_contDiffAt (B : RawAmbientBox E M)
    (b : Module.Basis ι ℝ (Plane × V)) {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι) (hinc : B.inclusion=ι) (hB : B.box.Smooth)
    {a : ℝ → M × V → (E × V) →L[ℝ] ℝ}
    (ha : SmoothOneFormFamily (fun t => semanticFullOneForm ι (a t)))
    {p : ℝ × (Plane × V)} (hp : p.2.1∈B.box.chart.target) :
    ContDiffAt ℝ ∞ (chartGram B b a) p := by
  have hf := B.fullForm_semantic_contDiffAt hι hinc hB ha hp
  apply ContDiffAt.pow _ 2
  unfold RawGram.gram
  simp only [Matrix.det_apply,Matrix.of_apply,Units.smul_def,zsmul_eq_mul]
  apply ContDiffAt.sum
  intro σ hσ
  exact contDiffAt_const.mul (contDiffAt_prod fun i hi =>
    (hf.clm_apply contDiffAt_const).clm_apply contDiffAt_const)

def weightedGram (B : RawAmbientBox E M) (b : Module.Basis ι ℝ (Plane × V))
    (a : ℝ → M × V → (E × V) →L[ℝ] ℝ) (p : ℝ × (M × V)) : ℝ := by
  classical
  exact if p.2.1∈B.box.chart.source then
    B.box.weight p.2.1 * chartGram B b a (p.1,(B.box.chart p.2.1,p.2.2)) else 0

theorem weightedGram_nonneg (B : RawAmbientBox E M) (b : Module.Basis ι ℝ (Plane × V))
    (a : ℝ → M × V → (E × V) →L[ℝ] ℝ) (p : ℝ × (M × V)) :
    0≤weightedGram B b a p := by
  unfold weightedGram
  split_ifs
  · exact mul_nonneg (B.box.weight_nonneg _) (sq_nonneg _)
  · exact le_rfl

theorem weightedGram_tsupport (B : RawAmbientBox E M) (b : Module.Basis ι ℝ (Plane × V))
    (a : ℝ → M × V → (E × V) →L[ℝ] ℝ) :
    tsupport (weightedGram B b a) ⊆ {p : ℝ × (M × V) | p.2.1∈tsupport B.box.weight} := by
  apply closure_minimal _ ((isClosed_tsupport _).preimage (continuous_fst.comp continuous_snd))
  intro p hp
  apply subset_closure
  intro hz
  apply hp
  unfold weightedGram
  split_ifs
  · exact mul_eq_zero_of_left hz _
  · rfl

theorem fullForm_isInvertible_iff (B : RawAmbientBox E M) {ι : M → E}
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ ι) (hinc : B.inclusion=ι) (hB : B.box.Smooth)
    (α : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm ι (α t)))
    (t : ℝ) {y : Plane × V} (hy : y.1∈B.box.chart.target) :
    (B.fullForm (α t) y).IsInvertible ↔
      (manifoldExteriorOneForm (semanticFullOneForm ι (α t))
        (flatProductMap B.box.chart.symm y)).IsInvertible := by
  let e : PartialDiffeomorph 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) M Plane ∞ :=
    { toPartialEquiv := B.box.chart.toPartialEquiv
      open_source := B.box.chart.open_source
      open_target := B.box.chart.open_target
      contMDiffOn_toFun := hB.forward
      contMDiffOn_invFun := hB.inverse }
  let cb : Plane ≃L[ℝ] Plane :=
    (PartialDiffeomorph.isLocalDiffeomorphAt 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) ∞ e.symm hy).mfderivToContinuousLinearEquiv (by simp)
  let c := cb.prodCongr (ContinuousLinearEquiv.refl ℝ V)
  have hc : (c : (Plane × V) →L[ℝ] (Plane × V)) =
      (mfderiv 𝓘(ℝ,Plane) 𝓘(ℝ,Plane) B.box.chart.symm y.1).prodMap
        (ContinuousLinearMap.id ℝ V) := rfl
  rw [B.fullForm_pullback hι hinc hB α hα t hy,←hc]
  exact bilinearComp_equiv_isInvertible_iff c

section manifold

theorem weightedGram_smooth_of_local (B : RawAmbientBox E M) (b : Module.Basis ι ℝ (Plane × V))
    (hB : B.box.Smooth) (hi : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {a : ℝ → M × V → (E × V) →L[ℝ] ℝ}
    (hloc : ∀ p : ℝ × (Plane × V),p.2.1∈B.box.chart.target → ContDiffAt ℝ ∞ (chartGram B b a) p) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞ (weightedGram B b a) := by
  apply contMDiff_of_tsupport
  intro p hp
  have hs := (B.box.weight_support (weightedGram_tsupport B b a hp)).1
  have hb := (hB.forward p.2.1 hs).contMDiffAt (B.box.chart.open_source.mem_nhds hs)
  have hfst : ContMDiffAt 𝓘(ℝ,Plane × V) 𝓘(ℝ,Plane) ∞
      (fun x : M × V => B.box.chart x.1) p.2 := hb.comp p.2 (flatProduct_fst_smooth.contMDiffAt)
  have hsnd := (flatProduct_snd_smooth (E:=Plane) (M:=M) (V:=V)).contMDiffAt (x:=p.2)
  have htime : ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞
      (Prod.fst : ℝ × (M × V) → ℝ) p := contMDiffAt_fst
  have harg : ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V))
      𝓘(ℝ,ℝ × (Plane × V)) ∞
      (fun q : ℝ × (M × V) => (q.1,(B.box.chart q.2.1,q.2.2))) p :=
    htime.prodMk_space ((hfst.prodMk_space hsnd).comp p contMDiffAt_snd)
  have hg := (hloc _ (B.box.chart.map_source hs)).contMDiffAt.comp p harg
  have hbase : ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,Plane) ∞
      (fun q : ℝ × (M × V) => q.2.1) p :=
    ((flatProduct_fst_smooth (E:=Plane) (M:=M) (V:=V)).contMDiffAt.comp p contMDiffAt_snd)
  have hw : ContMDiffAt ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞
      (fun q : ℝ × (M × V) => B.box.weight q.2.1) p :=
    (B.box.weight_smooth hB).contMDiffAt.comp p hbase
  apply (hw.mul hg).congr_of_eventuallyEq
  filter_upwards [(continuousAt_fst.comp continuousAt_snd).preimage_mem_nhds
    (B.box.chart.open_source.mem_nhds hs)] with q hq
  exact if_pos hq

end manifold

#check_explicit chartGram

variable {U : Set M}

def gramSum (D : RawSurfacePresentation E M U) (b : Module.Basis ι ℝ (Plane × V))
    (a : ℝ → M × V → (E × V) →L[ℝ] ℝ) (p : ℝ × (M × V)) : ℝ :=
  ∑ i, weightedGram (D.boxes i) b a p

def gramLevel (D : RawSurfacePresentation E M U) (b : Module.Basis ι ℝ (Plane × V))
    (a : ℝ → M × V → (E × V) →L[ℝ] ℝ) (K : Set (M × V)) : ℝ :=
  sInf (insert 1 (gramSum D b a '' (Icc (0:ℝ) 1 ×ˢ K)))

variable {κ : Type} [Fintype κ] [DecidableEq κ]

def fibreRadius (b : Module.Basis κ ℝ V) (K : Set (M × V)) : ℝ :=
  sSup (insert 0 ((fun x => RawGram.qn b x.2) '' K))

/-- A cutoff made from finitely many native chart determinants and explicit coordinate
plateaux. Its complete support is contained in the union of the supplied chart carriers. -/
def transferCut (D : RawSurfacePresentation E M U) (b : Module.Basis ι ℝ (Plane × V))
    (bv : Module.Basis κ ℝ V) (a : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (K : Set (M × V)) (p : ℝ × (M × V)) : ℝ :=
  Real.smoothTransition (4*gramSum D b a p/gramLevel D b a K-1) *
    Real.smoothTransition (3-p.1^2) *
    Real.smoothTransition (2*(fibreRadius bv K+1-RawGram.qn bv p.2.2))

theorem gramSum_source (D : RawSurfacePresentation E M U) (b : Module.Basis ι ℝ (Plane × V))
    (a : ℝ → M × V → (E × V) →L[ℝ] ℝ) {p : ℝ × (M × V)}
    (hp : 0<gramSum D b a p) : ∃ i,p.2.1∈(D.boxes i).box.chart.source := by
  by_contra hn
  push_neg at hn
  have hz : gramSum D b a p=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact if_neg (hn i)
  linarith

section manifold

theorem gramSum_semantic_smooth (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V))
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion)
    (hB : ∀ i,(D.boxes i).box.Smooth)
    (hi : ∀ i,ContDiffOn ℝ ∞ (D.boxes i).inverseAmbient (D.boxes i).box.chart.target)
    {a : ℝ → M × V → (E × V) →L[ℝ] ℝ}
    (ha : SmoothOneFormFamily (fun t => semanticFullOneForm D.inclusion (a t))) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞ (gramSum D b a) := by
  apply ContMDiff.sum
  intro i _
  exact weightedGram_smooth_of_local (D.boxes i) b (hB i) (hi i)
    (fun p hp => chartGram_semantic_contDiffAt (D.boxes i) b hι (D.box_inclusion i) (hB i) ha hp)

theorem weightedGram_pos_of_inner (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V))
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion)
    (hB : ∀ i,(D.boxes i).box.Smooth)
    (a : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm D.inclusion
      (a t)))
    {p : ℝ × (M × V)} (i : Fin (D.size+1)) (hp : p.2.1∈(D.boxes i).box.inner)
    (hinv : (manifoldExteriorOneForm (semanticFullOneForm D.inclusion
      (a p.1)) p.2).IsInvertible) :
    0<weightedGram (D.boxes i) b a p := by
  let B := D.boxes i
  have hs : p.2.1∈B.box.chart.source := by
    obtain ⟨y,hy,he⟩ := hp
    rw [←he]
    exact B.box.chart.map_target (B.box.closed_subset
      ((Metric.closedBall_subset_closedBall (by linarith [B.box.radius_pos])) hy))
  have hy : (B.box.chart p.2.1,p.2.2).1∈B.box.chart.target := B.box.chart.map_source hs
  have he : flatProductMap B.box.chart.symm (B.box.chart p.2.1,p.2.2)=p.2 := by
    exact Prod.ext (B.box.chart.left_inv hs) rfl
  have hi := (fullForm_isInvertible_iff B hι (D.box_inclusion i) (hB i)
    a hα p.1 hy).2 (he.symm ▸ hinv)

  unfold weightedGram
  rw [if_pos hs,B.box.weight_one p.2.1 hp,one_mul]
  unfold chartGram
  exact sq_pos_of_ne_zero (RawGram.gram_ne_zero_of_isInvertible b hi)

theorem gramSum_pos_of_cover (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V))
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion)
    (hB : ∀ i,(D.boxes i).box.Smooth)
    (a : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm D.inclusion
      (a t)))
    {p : ℝ × (M × V)} (hp : ∃ i,p.2.1∈(D.boxes i).box.inner)
    (hinv : (manifoldExteriorOneForm (semanticFullOneForm D.inclusion
      (a p.1)) p.2).IsInvertible) :
    0<gramSum D b a p := by
  obtain ⟨i,hi⟩ := hp
  exact (weightedGram_pos_of_inner D b hι hB a hα i hi hinv).trans_le
    (Finset.single_le_sum (fun j hj => weightedGram_nonneg _ _ _ _) (Finset.mem_univ i))

theorem gramSum_nondegenerate (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V))
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion)
    (hB : ∀ i,(D.boxes i).box.Smooth)
    (a : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm D.inclusion
      (a t)))
    {p : ℝ × (M × V)} (hp : 0<gramSum D b a p) :
    (manifoldExteriorOneForm (semanticFullOneForm D.inclusion
      (a p.1)) p.2).IsInvertible := by
  have hex : ∃ i,0<weightedGram (D.boxes i) b a p := by
    by_contra hn
    push_neg at hn
    exact not_lt_of_ge (Finset.sum_nonpos fun i hi => hn i) hp
  obtain ⟨i,hi⟩ := hex
  have hs : p.2.1∈(D.boxes i).box.chart.source := by
    by_contra hn
    simp only [weightedGram,if_neg hn] at hi
    exact lt_irrefl 0 hi
  have hgram : RawGram.gram b ((D.boxes i).fullForm
      (a p.1)
      ((D.boxes i).box.chart p.2.1,p.2.2)) ≠ 0 := by
    intro hz
    simp only [weightedGram,if_pos hs,chartGram,hz,zero_pow (by norm_num : 2≠0),mul_zero] at hi
    exact lt_irrefl 0 hi

  have he : flatProductMap (D.boxes i).box.chart.symm
      ((D.boxes i).box.chart p.2.1,p.2.2)=p.2 :=
    Prod.ext ((D.boxes i).box.chart.left_inv hs) rfl
  have h := (fullForm_isInvertible_iff (D.boxes i) hι (D.box_inclusion i) (hB i)
    a hα p.1
    ((D.boxes i).box.chart.map_source hs)).1 (RawGram.isInvertible_of_gram_ne_zero b hgram)
  rwa [he] at h

theorem gramLevel_pos (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V)) {a : ℝ → M × V → (E × V) →L[ℝ] ℝ}
    {K : Set (M × V)} (hK : IsCompact K) (hg : Continuous (gramSum D b a))
    (hpos : ∀ p∈Icc (0:ℝ) 1 ×ˢ K,0<gramSum D b a p) :
    0<gramLevel D b a K := by
  have hc := ((((isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).prod hK).image hg).insert (1:ℝ))
  have hm := hc.sInf_mem (Set.insert_nonempty _ _)
  rcases hm with h|⟨p,hp,he⟩
  · simpa only [gramLevel,h] using (show (0:ℝ)<1 by norm_num)
  · change 0<sInf (insert 1 (gramSum D b a '' (Icc (0:ℝ) 1 ×ˢ K)))
    rw [←he]
    exact hpos p hp

theorem gramLevel_le (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V)) {a : ℝ → M × V → (E × V) →L[ℝ] ℝ}
    {K : Set (M × V)} (hK : IsCompact K) (hg : Continuous (gramSum D b a))
    {p : ℝ × (M × V)} (hp : p∈Icc (0:ℝ) 1 ×ˢ K) :
    gramLevel D b a K≤gramSum D b a p :=
  csInf_le (((((isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).prod hK).image hg).insert (1:ℝ))).bddBelow
    (mem_insert_of_mem 1 ⟨p,hp,rfl⟩)

theorem fibreRadius_bound (bv : Module.Basis κ ℝ V) {K : Set (M × V)}
    (hK : IsCompact K) {x : M × V} (hx : x∈K) : RawGram.qn bv x.2≤fibreRadius bv K := by
  exact le_csSup ((hK.image ((RawGram.qn_contDiff bv).continuous.comp continuous_snd)).insert 0).bddAbove
    (mem_insert_of_mem 0 ⟨x,hx,rfl⟩)

theorem transferCut_one_near (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V)) (bv : Module.Basis κ ℝ V)
    (a : ℝ → M × V → (E × V) →L[ℝ] ℝ) {K : Set (M × V)}
    (hK : IsCompact K) (hg : Continuous (gramSum D b a)) (hμ : 0<gramLevel D b a K) :
    ∀ᶠ p in 𝓝ˢ (Icc (0:ℝ) 1 ×ˢ K),transferCut D b bv a K p=1 := by
  let O := {p : ℝ × (M × V) | gramLevel D b a K/2<gramSum D b a p ∧
    p.1^2<2 ∧ RawGram.qn bv p.2.2<fibreRadius bv K+1/2}
  have hqn : Continuous (fun p : ℝ × (M × V) => RawGram.qn bv p.2.2) :=
    (RawGram.qn_contDiff bv).continuous.comp (continuous_snd.comp continuous_snd)
  have hO : IsOpen O := (isOpen_lt continuous_const hg).inter
    ((isOpen_lt (continuous_fst.pow 2) continuous_const).inter (isOpen_lt hqn continuous_const))
  have hKO : Icc (0:ℝ) 1 ×ˢ K⊆O := by
    intro p hp
    have hm := gramLevel_le D b hK hg hp
    have hv := fibreRadius_bound bv hK hp.2
    refine ⟨by linarith,?_,by linarith⟩
    nlinarith [hp.1.1,hp.1.2]
  filter_upwards [hO.mem_nhdsSet.mpr hKO] with p hp
  unfold transferCut
  rw [Real.smoothTransition.one_of_one_le,
    Real.smoothTransition.one_of_one_le (by linarith [hp.2.1]),
    Real.smoothTransition.one_of_one_le (by linarith [hp.2.2])]
  · norm_num
  · rw [le_sub_iff_add_le,le_div_iff₀ hμ]
    linarith [hp.1]

theorem transferCut_smooth_of_gram (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V)) (bv : Module.Basis κ ℝ V)
    (a : ℝ → M × V → (E × V) →L[ℝ] ℝ) (K : Set (M × V))
    (hg : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞ (gramSum D b a)) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞ (transferCut D b bv a K) := by
  have hv : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,V) ∞
      (fun p : ℝ × (M × V) => p.2.2) :=
    (flatProduct_snd_smooth (E:=Plane) (M:=M) (V:=V)).comp contMDiff_snd
  have hqn := (RawGram.qn_contDiff bv).contMDiff.comp hv
  have h1 : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞
      (fun p => 4*gramSum D b a p/gramLevel D b a K-1) :=
    ((contMDiff_const.mul hg).div_const _).sub contMDiff_const
  have h2 : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × (M × V) => 3-p.1^2) := contMDiff_const.sub (contMDiff_fst.pow 2)
  have h3 : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × (M × V) => 2*(fibreRadius bv K+1-RawGram.qn bv p.2.2)) :=
    contMDiff_const.mul (contMDiff_const.sub hqn)
  exact (((Real.smoothTransition.contDiff.contMDiff.comp h1).mul
    (Real.smoothTransition.contDiff.contMDiff.comp h2)).mul
    (Real.smoothTransition.contDiff.contMDiff.comp h3))

theorem transferCut_semantic_smooth (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V)) (bv : Module.Basis κ ℝ V)
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion)
    (hB : ∀ i,(D.boxes i).box.Smooth)
    (hi : ∀ i,ContDiffOn ℝ ∞ (D.boxes i).inverseAmbient (D.boxes i).box.chart.target)
    {a : ℝ → M × V → (E × V) →L[ℝ] ℝ}
    (ha : SmoothOneFormFamily (fun t => semanticFullOneForm D.inclusion (a t))) (K : Set (M × V)) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞ (transferCut D b bv a K) :=
  transferCut_smooth_of_gram D b bv a K (gramSum_semantic_smooth D b hι hB hi ha)

theorem transferCut_tsupport_gram (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V)) (bv : Module.Basis κ ℝ V)
    (a : ℝ → M × V → (E × V) →L[ℝ] ℝ) (K : Set (M × V))
    (hg : Continuous (gramSum D b a)) (hμ : 0<gramLevel D b a K) :
    tsupport (transferCut D b bv a K) ⊆ {p | 0<gramSum D b a p} := by
  have hs : tsupport (transferCut D b bv a K) ⊆
      {p | gramLevel D b a K/4≤gramSum D b a p} := by
    apply closure_minimal _ (isClosed_le continuous_const hg)
    intro p hp
    by_contra hn
    change ¬gramLevel D b a K/4≤gramSum D b a p at hn
    have hgsmall : 4*gramSum D b a p/gramLevel D b a K-1≤0 := by
      rw [not_le] at hn
      have hh : 4*gramSum D b a p ≤ gramLevel D b a K := by linarith
      have hdiv := (div_le_one hμ).2 hh
      linarith
    apply hp
    simp only [transferCut,Real.smoothTransition.zero_of_nonpos hgsmall,zero_mul]
  intro p hp
  have hh := hs hp
  change gramLevel D b a K/4≤gramSum D b a p at hh
  change 0<gramSum D b a p
  linarith

theorem transferCut_tsupport_good (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V)) (bv : Module.Basis κ ℝ V)
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion)
    (hB : ∀ i,(D.boxes i).box.Smooth)
    (a : ℝ → M × V → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm D.inclusion
      (a t))) (K : Set (M × V))
    (hg : Continuous (gramSum D b a)) (hμ : 0<gramLevel D b a K)
    {p : ℝ × (M × V)} (hp : p∈tsupport (transferCut D b bv a K)) :
    (∃ i,p.2.1∈(D.boxes i).box.chart.source) ∧
      (manifoldExteriorOneForm (semanticFullOneForm D.inclusion
        (a p.1)) p.2).IsInvertible := by
  have hgpos := transferCut_tsupport_gram D b bv a K hg hμ hp
  exact ⟨gramSum_source D b a hgpos,gramSum_nondegenerate D b hι hB a hα hgpos⟩

def spatialCarrier (D : RawSurfacePresentation E M U) (bv : Module.Basis κ ℝ V)
    (K : Set (M × V)) : Set (M × V) :=
  (⋃ i,(D.boxes i).box.compactCarrier) ×ˢ {v | RawGram.qn bv v≤fibreRadius bv K+1}

theorem spatialCarrier_compact (D : RawSurfacePresentation E M U) (bv : Module.Basis κ ℝ V)
    (K : Set (M × V)) : IsCompact (spatialCarrier D bv K) :=
  (isCompact_iUnion fun i => (D.boxes i).box.compactCarrier_compact).prod
    (RawGram.isCompact_qn_le bv (fibreRadius bv K+1))

theorem transferCut_zero_off_carrier (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V)) (bv : Module.Basis κ ℝ V)
    (a : ℝ → M × V → (E × V) →L[ℝ] ℝ) (K : Set (M × V))
    (t : ℝ) (x : M × V) (hx : x∉spatialCarrier D bv K) : transferCut D b bv a K (t,x)=0 := by
  by_cases hb : x.1∈⋃ i,(D.boxes i).box.compactCarrier
  · have hv : fibreRadius bv K+1<RawGram.qn bv x.2 := by
      by_contra hn
      exact hx ⟨hb,not_lt.mp hn⟩
    have hz : 2*(fibreRadius bv K+1-RawGram.qn bv x.2)≤0 := by linarith
    simp only [transferCut,Real.smoothTransition.zero_of_nonpos hz,mul_zero]
  · have hw (i : Fin (D.size+1)) : (D.boxes i).box.weight x.1=0 := by
      by_contra hn
      have ht : x.1∈tsupport (D.boxes i).box.weight := subset_closure hn
      exact hb (mem_iUnion.mpr ⟨i,(D.boxes i).box.carrier_subset_compactCarrier
        ((D.boxes i).box.weight_support ht)⟩)
    have hg : gramSum D b a (t,x)=0 := by
      apply Finset.sum_eq_zero
      intro i hi
      unfold weightedGram
      split_ifs <;> simp only [hw,zero_mul]
    simp only [transferCut,hg,mul_zero,zero_div,zero_sub,
      Real.smoothTransition.zero_of_nonpos (by norm_num : (-1:ℝ)≤0),zero_mul]

theorem transferCut_fibreCompact (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V)) (bv : Module.Basis κ ℝ V)
    (a : ℝ → M × V → (E × V) →L[ℝ] ℝ) (K : Set (M × V)) :
    ∃ C : Set V,IsCompact C ∧ ∀ t x,x.2∉C → transferCut D b bv a K (t,x)=0 := by
  refine ⟨{v | RawGram.qn bv v≤fibreRadius bv K+1},
    RawGram.isCompact_qn_le bv _,?_⟩
  intro t x hx
  have hv : fibreRadius bv K+1<RawGram.qn bv x.2 := not_le.mp hx
  have hz : 2*(fibreRadius bv K+1-RawGram.qn bv x.2)≤0 := by linarith
  simp only [transferCut,Real.smoothTransition.zero_of_nonpos hz,mul_zero]

end manifold

#check_explicit weightedGram
#check_explicit gramSum
#check_explicit gramLevel
#check_explicit transferCut
end SymplecticPacking.HighDim.ToricPackingStages.NativePathCutoff
