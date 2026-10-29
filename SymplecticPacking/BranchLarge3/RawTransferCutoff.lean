import SymplecticPacking.BranchLarge3.UniformMoser
import SymplecticPacking.BranchLarge3.ExactSafety
import SymplecticPacking.HighDim.Handle.RawFullProductMoserSpec

/-!
# Chart Gram functions for the transfer cutoff

Finite chart Gram functions for the native six-dimensional transfer cutoff.
-/

noncomputable section
namespace SymplecticPacking.BranchLarge3.RawTransfer
open Set Function Manifold Filter
open OAI.PackingSufficiencySupport.Hamiltonian
open HighDim.ToricPackingStages
open scoped ContDiff Manifold Topology

variable {E M V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace M] [T2Space M]

theorem fullCovector_contDiffAt (B : RawAmbientBox E M)
    (hB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ a)
    {p : ℝ × (Plane × V)} (hp : p.2.1∈B.box.chart.target) :
    ContDiffAt ℝ ∞ (fun q : ℝ × (Plane × V) =>
      B.fullCovector (fun x => a (q.1,(B.inclusion x.1,x.2))) q.2) p := by
  have hi₀ : ContDiffAt ℝ ∞ B.inverseAmbient p.2.1 :=
    (hB p.2.1 hp).contDiffAt (B.box.chart.open_target.mem_nhds hp)
  have hi : ContDiffAt ℝ ∞ (fun q : ℝ × (Plane × V) => B.inverseAmbient q.2.1) p :=
    ContDiffAt.comp (g:=B.inverseAmbient) (f:=fun q : ℝ × (Plane × V) => q.2.1)
      p hi₀ contDiffAt_snd.fst
  have hf₀ : ContDiffAt ℝ ∞ B.frame p.2.1 :=
    (((hB.fderiv_of_isOpen B.box.chart.open_target (by simp)) p.2.1 hp).contDiffAt
      (B.box.chart.open_target.mem_nhds hp))
  have hf : ContDiffAt ℝ ∞ (fun q : ℝ × (Plane × V) => B.frame q.2.1) p :=
    ContDiffAt.comp (g:=B.frame) (f:=fun q : ℝ × (Plane × V) => q.2.1)
      p hf₀ contDiffAt_snd.fst
  have hframe : ContDiffAt ℝ ∞ (fun q : ℝ × (Plane × V) =>
      (B.frame q.2.1).prodMap (ContinuousLinearMap.id ℝ V)) p :=
    (ContinuousLinearMap.prodMapL ℝ Plane E V V).contDiff.contDiffAt.comp p
      (hf.prodMk contDiffAt_const)
  exact (ha.contDiffAt.comp p (contDiffAt_fst.prodMk (hi.prodMk contDiffAt_snd.snd))).clm_comp hframe

theorem fullForm_contDiffAt (B : RawAmbientBox E M)
    (hB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ a)
    {p : ℝ × (Plane × V)} (hp : p.2.1∈B.box.chart.target) :
    ContDiffAt ℝ ∞ (fun q : ℝ × (Plane × V) =>
      B.fullForm (fun x => a (q.1,(B.inclusion x.1,x.2))) q.2) p := by
  have hc := fullCovector_contDiffAt B hB ha hp
  have hraw : ContDiffAt ℝ ∞ (fun q : (ℝ × (Plane × V)) × (Plane × V) =>
      B.fullCovector (fun x => a (q.1.1,(B.inclusion x.1,x.2))) q.2) (p,p.2) := by
    exact hc.comp (p,p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  have hd : ContDiffAt ℝ ∞ (fun q : ℝ × (Plane × V) =>
      fderiv ℝ (B.fullCovector (fun x => a (q.1,(B.inclusion x.1,x.2)))) q.2) p :=
    hraw.fderiv contDiffAt_snd (by simp)
  have hflip : ContDiff ℝ ∞ (fun L : (Plane × V) →L[ℝ] (Plane × V) →L[ℝ] ℝ => L.flip) :=
    LinearIsometryEquiv.contDiff (𝕜:=ℝ) (n:=∞)
      (E:=(Plane × V) →L[ℝ] (Plane × V) →L[ℝ] ℝ)
      (F:=(Plane × V) →L[ℝ] (Plane × V) →L[ℝ] ℝ)
      (ContinuousLinearMap.flipₗᵢ ℝ (Plane × V) (Plane × V) ℝ)
  exact hd.sub (hflip.contDiffAt.comp p hd)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def chartGram (B : RawAmbientBox E M) (b : Module.Basis ι ℝ (Plane × V))
    (a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ) (p : ℝ × (Plane × V)) : ℝ :=
  UMoser.gram b (B.fullForm (fun x => a (p.1,(B.inclusion x.1,x.2))) p.2)^2

theorem chartGram_contDiffAt (B : RawAmbientBox E M)
    (b : Module.Basis ι ℝ (Plane × V))
    (hB : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ a)
    {p : ℝ × (Plane × V)} (hp : p.2.1∈B.box.chart.target) :
    ContDiffAt ℝ ∞ (chartGram B b a) p := by
  have hf := fullForm_contDiffAt B hB ha hp
  apply ContDiffAt.pow _ 2
  unfold UMoser.gram
  simp only [Matrix.det_apply,Matrix.of_apply,Units.smul_def,zsmul_eq_mul]
  apply ContDiffAt.sum
  intro σ hσ
  exact contDiffAt_const.mul (contDiffAt_prod fun i hi =>
    (hf.clm_apply contDiffAt_const).clm_apply contDiffAt_const)

/-- The chart determinant is multiplied by a bump whose closed support is strictly inside
that same chart. This formula is a genuine zero extension. -/
def weightedGram (B : RawAmbientBox E M) (b : Module.Basis ι ℝ (Plane × V))
    (a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ) (p : ℝ × (M × V)) : ℝ := by
  classical
  exact if p.2.1∈B.box.chart.source then
    B.box.weight p.2.1 * chartGram B b a (p.1,(B.box.chart p.2.1,p.2.2)) else 0

theorem weightedGram_nonneg (B : RawAmbientBox E M) (b : Module.Basis ι ℝ (Plane × V))
    (a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ) (p : ℝ × (M × V)) :
    0≤weightedGram B b a p := by
  unfold weightedGram
  split_ifs
  · exact mul_nonneg (B.box.weight_nonneg _) (sq_nonneg _)
  · exact le_rfl

theorem weightedGram_tsupport (B : RawAmbientBox E M) (b : Module.Basis ι ℝ (Plane × V))
    (a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ) :
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

section manifold
variable [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
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

theorem weightedGram_smooth (B : RawAmbientBox E M) (b : Module.Basis ι ℝ (Plane × V))
    (hB : B.box.Smooth) (hi : ContDiffOn ℝ ∞ B.inverseAmbient B.box.chart.target)
    {a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ a) :
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
  have hg := (chartGram_contDiffAt B b hi ha (B.box.chart.map_source hs)).contMDiffAt.comp p harg
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
    (a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ) (p : ℝ × (M × V)) : ℝ :=
  ∑ i, weightedGram (D.boxes i) b a p

def gramLevel (D : RawSurfacePresentation E M U) (b : Module.Basis ι ℝ (Plane × V))
    (a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ) (K : Set (M × V)) : ℝ :=
  sInf (insert 1 ((fun x => gramSum D b a (0,x)) '' K))

variable {κ : Type} [Fintype κ] [DecidableEq κ]

def fibreRadius (b : Module.Basis κ ℝ V) (K : Set (M × V)) : ℝ :=
  sSup (insert 0 ((fun x => UMoser.qn b x.2) '' K))

/-- A cutoff made from finitely many native chart determinants and explicit coordinate
plateaux. Its complete support is contained in the union of the supplied chart carriers. -/
def transferCut (D : RawSurfacePresentation E M U) (b : Module.Basis ι ℝ (Plane × V))
    (bv : Module.Basis κ ℝ V) (a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ)
    (K : Set (M × V)) (p : ℝ × (M × V)) : ℝ :=
  Real.smoothTransition (4*gramSum D b a p/gramLevel D b a K-1) *
    Real.smoothTransition (2-p.1^2) *
    Real.smoothTransition (2*(fibreRadius bv K+1-UMoser.qn bv p.2.2))

theorem gramSum_source (D : RawSurfacePresentation E M U) (b : Module.Basis ι ℝ (Plane × V))
    (a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ) {p : ℝ × (M × V)}
    (hp : 0<gramSum D b a p) : ∃ i,p.2.1∈(D.boxes i).box.chart.source := by
  by_contra hn
  push_neg at hn
  have hz : gramSum D b a p=0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact if_neg (hn i)
  linarith

section manifold
variable [ChartedSpace Plane M] [IsManifold 𝓘(ℝ,Plane) ∞ M]

theorem gramSum_smooth (D : RawSurfacePresentation E M U) (b : Module.Basis ι ℝ (Plane × V))
    (hB : ∀ i,(D.boxes i).box.Smooth)
    (hi : ∀ i,ContDiffOn ℝ ∞ (D.boxes i).inverseAmbient (D.boxes i).box.chart.target)
    {a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ a) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞ (gramSum D b a) :=
  ContMDiff.sum fun i hi' => weightedGram_smooth (D.boxes i) b (hB i) (hi i) ha

variable [FiniteDimensional ℝ V]

theorem weightedGram_pos_of_inner (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V))
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion)
    (hB : ∀ i,(D.boxes i).box.Smooth)
    (a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm D.inclusion
      (fun x => a (t,(D.inclusion x.1,x.2)))))
    {p : ℝ × (M × V)} (i : Fin (D.size+1)) (hp : p.2.1∈(D.boxes i).box.inner)
    (hinv : (manifoldExteriorOneForm (semanticFullOneForm D.inclusion
      (fun x => a (p.1,(D.inclusion x.1,x.2)))) p.2).IsInvertible) :
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
    (fun t x => a (t,(D.inclusion x.1,x.2))) hα p.1 hy).2 (he.symm ▸ hinv)
  have hval : (fun x : M × V => a (p.1,((D.boxes i).inclusion x.1,x.2))) =
      (fun x : M × V => a (p.1,(D.inclusion x.1,x.2))) := by rw [D.box_inclusion i]
  unfold weightedGram
  rw [if_pos hs,B.box.weight_one p.2.1 hp,one_mul]
  unfold chartGram
  rw [hval]
  exact sq_pos_of_ne_zero (UMoser.gram_ne_zero_of_isInvertible b hi)

theorem gramSum_pos_of_cover (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V))
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion)
    (hB : ∀ i,(D.boxes i).box.Smooth)
    (a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm D.inclusion
      (fun x => a (t,(D.inclusion x.1,x.2)))))
    {p : ℝ × (M × V)} (hp : ∃ i,p.2.1∈(D.boxes i).box.inner)
    (hinv : (manifoldExteriorOneForm (semanticFullOneForm D.inclusion
      (fun x => a (p.1,(D.inclusion x.1,x.2)))) p.2).IsInvertible) :
    0<gramSum D b a p := by
  obtain ⟨i,hi⟩ := hp
  exact (weightedGram_pos_of_inner D b hι hB a hα i hi hinv).trans_le
    (Finset.single_le_sum (fun j hj => weightedGram_nonneg _ _ _ _) (Finset.mem_univ i))

theorem gramSum_nondegenerate (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V))
    (hι : ContMDiff 𝓘(ℝ,Plane) 𝓘(ℝ,E) ∞ D.inclusion)
    (hB : ∀ i,(D.boxes i).box.Smooth)
    (a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm D.inclusion
      (fun x => a (t,(D.inclusion x.1,x.2)))))
    {p : ℝ × (M × V)} (hp : 0<gramSum D b a p) :
    (manifoldExteriorOneForm (semanticFullOneForm D.inclusion
      (fun x => a (p.1,(D.inclusion x.1,x.2)))) p.2).IsInvertible := by
  have hex : ∃ i,0<weightedGram (D.boxes i) b a p := by
    by_contra hn
    push_neg at hn
    exact not_lt_of_ge (Finset.sum_nonpos fun i hi => hn i) hp
  obtain ⟨i,hi⟩ := hex
  have hs : p.2.1∈(D.boxes i).box.chart.source := by
    by_contra hn
    simp only [weightedGram,if_neg hn] at hi
    exact lt_irrefl 0 hi
  have hgram : UMoser.gram b ((D.boxes i).fullForm
      (fun x => a (p.1,((D.boxes i).inclusion x.1,x.2)))
      ((D.boxes i).box.chart p.2.1,p.2.2)) ≠ 0 := by
    intro hz
    simp only [weightedGram,if_pos hs,chartGram,hz,zero_pow (by norm_num : 2≠0),mul_zero] at hi
    exact lt_irrefl 0 hi
  have hval : (fun x : M × V => a (p.1,((D.boxes i).inclusion x.1,x.2))) =
      (fun x : M × V => a (p.1,(D.inclusion x.1,x.2))) := by rw [D.box_inclusion i]
  rw [hval] at hgram
  have he : flatProductMap (D.boxes i).box.chart.symm
      ((D.boxes i).box.chart p.2.1,p.2.2)=p.2 :=
    Prod.ext ((D.boxes i).box.chart.left_inv hs) rfl
  have h := (fullForm_isInvertible_iff (D.boxes i) hι (D.box_inclusion i) (hB i)
    (fun t x => a (t,(D.inclusion x.1,x.2))) hα p.1
    ((D.boxes i).box.chart.map_source hs)).1 (UMoser.isInvertible_of_gram_ne_zero b hgram)
  rwa [he] at h

theorem gramLevel_pos (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V)) {a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ}
    {K : Set (M × V)} (hK : IsCompact K)
    (hg : Continuous (gramSum D b a)) (hpos : ∀ x∈K,0<gramSum D b a (0,x)) :
    0<gramLevel D b a K := by
  let f : Fin 1 → ℝ × (M × V) → ℝ := fun _ => gramSum D b a
  have hh := ExactSafety.clearance_pos (f:=f) hK
    (fun i => (hg.comp (continuous_const.prodMk continuous_id)).continuousOn)
    (fun i => hpos)
  simpa only [ExactSafety.clearance,ExactSafety.initialValues,f,iUnion_const,gramLevel] using hh

theorem gramLevel_le (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V)) {a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ}
    {K : Set (M × V)} (hK : IsCompact K) (hg : Continuous (gramSum D b a))
    {x : M × V} (hx : x∈K) : gramLevel D b a K≤gramSum D b a (0,x) := by
  exact csInf_le ((hK.image (hg.comp (continuous_const.prodMk continuous_id))).insert 1).bddBelow
    (mem_insert_of_mem 1 ⟨x,hx,rfl⟩)

theorem fibreRadius_bound (bv : Module.Basis κ ℝ V) {K : Set (M × V)}
    (hK : IsCompact K) {x : M × V} (hx : x∈K) : UMoser.qn bv x.2≤fibreRadius bv K := by
  exact le_csSup ((hK.image ((UMoser.qn_contDiff bv).continuous.comp continuous_snd)).insert 0).bddAbove
    (mem_insert_of_mem 0 ⟨x,hx,rfl⟩)

theorem transferCut_smooth (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V)) (bv : Module.Basis κ ℝ V)
    (hB : ∀ i,(D.boxes i).box.Smooth)
    (hi : ∀ i,ContDiffOn ℝ ∞ (D.boxes i).inverseAmbient (D.boxes i).box.chart.target)
    {a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ} (ha : ContDiff ℝ ∞ a) (K : Set (M × V)) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞ (transferCut D b bv a K) := by
  have hg := gramSum_smooth D b hB hi ha
  have hv : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,V) ∞
      (fun p : ℝ × (M × V) => p.2.2) :=
    (flatProduct_snd_smooth (E:=Plane) (M:=M) (V:=V)).comp contMDiff_snd
  have hqn := (UMoser.qn_contDiff bv).contMDiff.comp hv
  have h1 : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞
      (fun p => 4*gramSum D b a p/gramLevel D b a K-1) :=
    ((contMDiff_const.mul hg).div_const _).sub contMDiff_const
  have h2 : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × (M × V) => 2-p.1^2) := contMDiff_const.sub (contMDiff_fst.pow 2)
  have h3 : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,Plane × V)) 𝓘(ℝ,ℝ) ∞
      (fun p : ℝ × (M × V) => 2*(fibreRadius bv K+1-UMoser.qn bv p.2.2)) :=
    contMDiff_const.mul (contMDiff_const.sub hqn)
  exact (((Real.smoothTransition.contDiff.contMDiff.comp h1).mul
    (Real.smoothTransition.contDiff.contMDiff.comp h2)).mul
    (Real.smoothTransition.contDiff.contMDiff.comp h3))

theorem transferCut_tsupport_gram (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V)) (bv : Module.Basis κ ℝ V)
    (a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ) (K : Set (M × V))
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
    (a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ)
    (hα : SmoothOneFormFamily (fun t => semanticFullOneForm D.inclusion
      (fun x => a (t,(D.inclusion x.1,x.2))))) (K : Set (M × V))
    (hg : Continuous (gramSum D b a)) (hμ : 0<gramLevel D b a K)
    {p : ℝ × (M × V)} (hp : p∈tsupport (transferCut D b bv a K)) :
    (∃ i,p.2.1∈(D.boxes i).box.chart.source) ∧
      (manifoldExteriorOneForm (semanticFullOneForm D.inclusion
        (fun x => a (p.1,(D.inclusion x.1,x.2)))) p.2).IsInvertible := by
  have hgpos := transferCut_tsupport_gram D b bv a K hg hμ hp
  exact ⟨gramSum_source D b a hgpos,gramSum_nondegenerate D b hι hB a hα hgpos⟩

def spatialCarrier (D : RawSurfacePresentation E M U) (bv : Module.Basis κ ℝ V)
    (K : Set (M × V)) : Set (M × V) :=
  (⋃ i,(D.boxes i).box.compactCarrier) ×ˢ {v | UMoser.qn bv v≤fibreRadius bv K+1}

theorem spatialCarrier_compact (D : RawSurfacePresentation E M U) (bv : Module.Basis κ ℝ V)
    (K : Set (M × V)) : IsCompact (spatialCarrier D bv K) :=
  (isCompact_iUnion fun i => (D.boxes i).box.compactCarrier_compact).prod
    (UMoser.isCompact_qn_le bv (fibreRadius bv K+1))

theorem transferCut_zero_off_carrier (D : RawSurfacePresentation E M U)
    (b : Module.Basis ι ℝ (Plane × V)) (bv : Module.Basis κ ℝ V)
    (a : ℝ × (E × V) → (E × V) →L[ℝ] ℝ) (K : Set (M × V))
    (t : ℝ) (x : M × V) (hx : x∉spatialCarrier D bv K) : transferCut D b bv a K (t,x)=0 := by
  by_cases hb : x.1∈⋃ i,(D.boxes i).box.compactCarrier
  · have hv : fibreRadius bv K+1<UMoser.qn bv x.2 := by
      by_contra hn
      exact hx ⟨hb,not_lt.mp hn⟩
    have hz : 2*(fibreRadius bv K+1-UMoser.qn bv x.2)≤0 := by linarith
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

end manifold

#check_explicit weightedGram
#check_explicit gramSum
#check_explicit gramLevel
#check_explicit transferCut
end SymplecticPacking.BranchLarge3.RawTransfer
