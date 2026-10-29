import SymplecticPacking.General.Compile
import SymplecticPacking.General.TargetShrink

/-!
# Existence of compilation data

Existence of all finite-compilation bounds and rational samples from a smooth
spatially compact packing. All choices in this file are confined to propositions.
-/

noncomputable section
namespace SymplecticPacking.General.Compile
open Set Metric Filter Problem
open scoped ContDiff Topology

private theorem finite_compact_bound {X ι : Type*} [TopologicalSpace X] [Fintype ι]
    {K : Set X} (hK : IsCompact K) (f : ι → X → ℝ) (hf : ∀ i,Continuous (f i)) :
    ∃ R : ℝ,1≤R ∧ ∀ i,∀ x∈K,|f i x|≤R := by
  classical
  have hb : ∀ i,∃ b : ℝ,∀ x∈K,|f i x|≤b := by
    intro i
    obtain ⟨b,hb⟩ := hK.bddAbove_image (hf i).abs.continuousOn
    exact ⟨b,fun x hx => hb ⟨x,hx,rfl⟩⟩
  choose b hb using hb
  refine ⟨1+∑ i,|b i|,?_,?_⟩
  · have hh := Finset.sum_nonneg (s:=Finset.univ) (fun i _ => abs_nonneg (b i))
    linarith
  intro i x hx
  have hh := Finset.single_le_sum (f:=fun i => |b i|) (fun j _ => abs_nonneg (b j))
    (Finset.mem_univ i)
  exact (hb i x hx).trans ((le_abs_self _).trans (by linarith))

private theorem supported_family_bound {X Y : Type*} [NormedAddCommGroup X]
    [NormedAddCommGroup Y] {K : Set X} (hK : IsCompact K) (f : ℝ × X → Y)
    (hf : Continuous f) (hz : ∀ t,∀ x∉K,f (t,x)=0) :
    ∃ R : ℝ,1≤R ∧ ∀ t∈Icc (0:ℝ) 1,∀ x,1+‖f (t,x)‖≤R := by
  obtain ⟨b,hb⟩ := (isCompact_Icc.prod hK).bddAbove_image hf.norm.continuousOn
  refine ⟨max 1 (1+b),le_max_left _ _,?_⟩
  intro t ht x
  by_cases hx : x∈K
  · have hh : ‖f (t,x)‖≤b := hb ⟨(t,x),⟨ht,hx⟩,rfl⟩
    exact (by linarith : 1+‖f (t,x)‖≤1+b).trans (le_max_right _ _)
  · rw [hz t x hx,norm_zero,add_zero]
    exact le_max_left _ _

private theorem spatial_derivative_smooth {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {H : ℝ → X → Y} (hH : ContDiff ℝ ∞ (Function.uncurry H)) :
    ContDiff ℝ ∞ (fun p : ℝ × X => fderiv ℝ (H p.1) p.2) := by
  let f : (ℝ × X) → X → Y := fun p x => H p.1 x
  have hf : ContDiff ℝ ∞ (Function.uncurry f) :=
    hH.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact hf.fderiv contDiff_snd (by simp)

private theorem derivative_zero_off {X Y : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {K : Set X} (hK : IsClosed K) {f : X → Y} (hf : ∀ x∉K,f x=0)
    {x : X} (hx : x∉K) : fderiv ℝ f x=0 := by
  apply fderiv_of_notMem_tsupport ℝ
  have hs : tsupport f⊆K := closure_minimal (fun z hz => by
    by_contra h
    exact hz (hf z h)) hK
  exact fun h => hx (hs h)

private theorem cpd_smooth {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (j : Fin d) : ContDiff ℝ ∞ (cpd f j) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

private theorem cube_closedBall {d : ℕ} : cube d⊆closedBall (0:Fin d→ℝ) 1 := by
  intro x hx
  rw [mem_closedBall_zero_iff]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  rw [Real.norm_eq_abs,abs_of_nonneg (hx j).1]
  exact (hx j).2

private theorem cube_jet_bound {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ∃ M : ℝ,1≤M ∧ (∀ x∈cube d,∀ j,|cpd f j x|≤M) ∧
      (∀ x∈cube d,∀ j l,|cpd (cpd f j) l x|≤M) := by
  let g : (Fin d ⊕ (Fin d × Fin d)) → (Fin d → ℝ) → ℝ :=
    Sum.elim (fun j => cpd f j) (fun jl => cpd (cpd f jl.1) jl.2)
  have hg : ∀ i,Continuous (g i) := by
    intro i
    cases i with
    | inl j => exact (cpd_smooth hf j).continuous
    | inr jl => exact (cpd_smooth (cpd_smooth hf jl.1) jl.2).continuous
  obtain ⟨M,hM,hgM⟩ := finite_compact_bound (isCompact_closedBall (0:Fin d→ℝ) 1) g hg
  exact ⟨M,hM,fun x hx j => hgM (Sum.inl j) x (cube_closedBall hx),
    fun x hx j l => hgM (Sum.inr (j,l)) x (cube_closedBall hx)⟩

/-- Every smooth spatially compact packing has finite compilation data.
The spatial plateau may be prescribed arbitrarily large and the rational accuracy arbitrarily
small. This is an existence theorem, not an evaluator or a new input oracle. -/
theorem exists_compilationDatum_with_margin {n k : ℕ} {C₀ C : ℝ} {c : Fin k → ℝ} {s : Fin k → E n}
    {H : ℝ → E n → ℝ} (hpack : PackingSpec n k C₀ c s H) (hC₀ : 0<C₀) (hC : C₀<C)
    (Bmin : ℕ) (ε : ℚ) (hε : 0<ε) :
    ∃ D : CompilationDatum n k C c s H, Bmin<D.B ∧ D.δ<ε ∧
      2*((2*n+1:ℕ):ℝ)*(D.Sbox:ℝ)+4<D.B ∧ D.C₀=C₀ ∧ D.bR<ε := by
  classical
  obtain ⟨K,hK,hzero⟩ := hpack.compactSupport
  -- A uniform spatial support box.
  obtain ⟨R,hR,hRK⟩ := finite_compact_bound hK
    (fun l : Fin (2*n) => fun z : E n => z l)
    (fun l => (EuclideanSpace.proj l : E n →L[ℝ] ℝ).continuous)
  obtain ⟨Sbox,hSbox⟩ := exists_rat_gt R
  have hSpos : (0:ℝ)<Sbox := by linarith
  have hsupport : ∀ t (z : E n), (∃ l,(Sbox:ℝ)≤|z l|) → H t z=0 := by
    intro t z hz
    apply hzero t z
    intro hzK
    obtain ⟨l,hl⟩ := hz
    linarith [hRK l z hzK]
  obtain ⟨B,hB⟩ := exists_nat_gt
    (max ((2*n:ℕ):ℝ) (max (2*((2*n+1:ℕ):ℝ)*(Sbox:ℝ)+4) (Bmin:ℝ)))
  have hBd : (2*n:ℕ)<B := by
    exact_mod_cast (lt_of_le_of_lt (le_max_left _ _) hB)
  have hBlarge : 2*((2*n+1:ℕ):ℝ)*(Sbox:ℝ)+4<B :=
    (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hB)
  have hBbox : 2*(Sbox:ℝ)<B := by
    have hn : (1:ℝ)≤((2*n+1:ℕ):ℝ) := by exact_mod_cast (show 1≤2*n+1 by omega)
    have hh := mul_le_mul_of_nonneg_right hn hSpos.le
    nlinarith
  have hBmin : Bmin<B := by
    exact_mod_cast ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hB))
  have hBr : (0:ℝ)<B := by exact_mod_cast (show 0<B by omega)
  -- Uniform Hessian bound on the compact spatial support, and zero off it.
  have hD1 : ContDiff ℝ ∞ (fun p : ℝ × E n => fderiv ℝ (H p.1) p.2) :=
    spatial_derivative_smooth hpack.smooth
  have hD2 : ContDiff ℝ ∞ (fun p : ℝ × E n => fderiv ℝ (fderiv ℝ (H p.1)) p.2) :=
    spatial_derivative_smooth (H:=fun t z => fderiv ℝ (H t) z) hD1
  have hD2zero : ∀ t,∀ z∉K,fderiv ℝ (fderiv ℝ (H t)) z=0 := by
    intro t z hz
    exact derivative_zero_off hK.isClosed
      (fun w hw => derivative_zero_off hK.isClosed (hzero t) hw) hz
  obtain ⟨LX,hLX,hLXge⟩ := supported_family_bound hK
    (fun p : ℝ × E n => fderiv ℝ (fderiv ℝ (H p.1)) p.2) hD2.continuous hD2zero
  -- The cutoff gradient has compact support as well.
  let Rβ : ℝ := 2*n*(3*(B:ℝ)/4)
  let Kβ : Set (E n) := closedBall 0 Rβ
  have hβzero : ∀ z∉Kβ,boxCut n B z=0 := by
    intro z hz
    have hn : Rβ<‖z‖ := by simpa only [Kβ,mem_closedBall,dist_zero_right,not_le] using hz
    exact support_of_coords (f:=fun (_:ℝ) z => boxCut n B z) (by positivity)
      (fun _ w hw => by obtain ⟨l,hl⟩ := hw; exact boxCut_eq_zero hBr hl) 0 z hn
  have hβder : ∀ (t:ℝ),∀ z∉Kβ,fderiv ℝ (boxCut n (B:ℝ)) z=0 :=
    fun _ _ hz => derivative_zero_off isClosed_closedBall hβzero hz
  obtain ⟨Cβ,hCβ,hCβge⟩ := supported_family_bound (isCompact_closedBall (0:E n) Rβ)
    (fun p : ℝ × E n => fderiv ℝ (boxCut n (B:ℝ)) p.2)
    (((contDiff_boxCut (n:=n) B).fderiv_right (m:=∞) (by simp)).continuous.comp continuous_snd) hβder
  -- Strict radial and approximation margins.
  have hgap : 0<(Real.sqrt (C/Real.pi)-Real.sqrt (C₀/Real.pi))/4 := by
    have hh := Real.sqrt_lt_sqrt (by positivity : 0≤C₀/Real.pi)
      ((div_lt_div_iff_of_pos_right Real.pi_pos).mpr hC)
    linarith
  obtain ⟨bR,hbR0,hbRmin⟩ := exists_rat_btwn
    (lt_min (show (0:ℝ)<ε by exact_mod_cast hε) hgap)
  have hbR : (bR:ℝ)<(Real.sqrt (C/Real.pi)-Real.sqrt (C₀/Real.pi))/4 :=
    hbRmin.trans_le (min_le_right _ _)
  have hbRε : bR<ε := by
    have hh : (bR:ℝ)<(ε:ℝ) := hbRmin.trans_le (min_le_left _ _)
    exact_mod_cast hh
  have hbRpos : 0<bR := by exact_mod_cast hbR0
  obtain ⟨M₀,hM₀,hM1,hM2⟩ := cube_jet_bound (contDiff_Htilde hpack.smooth (B:ℝ))
  have htol : 0 < min (1/2:ℝ) (min
      ((bR:ℝ)*Real.exp (-LX)/2/(16*(1+Cβ))) (ε:ℝ)) := by
    apply lt_min (by norm_num)
    apply lt_min
    · positivity
    · exact_mod_cast hε
  obtain ⟨δ,hδ0,hδ⟩ := exists_rat_btwn htol
  have hδpos : 0<δ := by exact_mod_cast hδ0
  have hδhalf : δ<1/2 := by
    have hh : (δ:ℝ)<((1/2:ℚ):ℝ) := by
      norm_num
      exact hδ.trans_le (min_le_left _ _)
    exact_mod_cast hh
  have hδsmall : (δ:ℝ)<(bR:ℝ)*Real.exp (-LX)/2/(16*(1+Cβ)) :=
    hδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδε : δ<ε := by
    exact_mod_cast hδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨N,hN⟩ := exists_nat_gt (max (1:ℝ)
    (max (((2*n+1)*M₀/(δ:ℝ))^2) (4*M₀/(δ:ℝ))))
  have hN1 : 1<N := by exact_mod_cast (le_max_left _ _).trans_lt hN
  have hNsq : ((2*n+1)*M₀/(δ:ℝ))^2<N :=
    (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hN)
  have hNlin : 4*M₀/(δ:ℝ)<N :=
    (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hN)
  -- Rational density supplies the finitely many samples in the proposition.
  have hsamples : ∀ m : Fin (2*n+1) → Fin (N+1),∃ q : ℚ,
      |(q:ℝ)-Htilde n B H (SymplecticPacking.gridPt N m)|<(δ:ℝ)/(2*N+1) := by
    intro m
    let x := Htilde n B H (SymplecticPacking.gridPt N m)
    have hτ : 0<(δ:ℝ)/(2*N+1) := by positivity
    obtain ⟨q,hq1,hq2⟩ := exists_rat_btwn
      (show x-(δ:ℝ)/(2*N+1)<x+(δ:ℝ)/(2*N+1) by linarith)
    exact ⟨q,abs_lt.mpr ⟨by linarith,by linarith⟩⟩
  choose Hm hHm using hsamples
  let D : CompilationDatum n k C c s H :=
    { C₀:=C₀,C₀_pos:=hC₀,C₀_lt:=hC,image:=image_of_packingSpec hpack
      Sbox:=Sbox,Sbox_pos:=by exact_mod_cast hSpos,support:=hsupport
      B:=B,B_gt_dim:=hBd,B_gt_box:=hBbox
      LX:=LX,LX_ge:=hLXge,Cβ:=Cβ,Cβ_ge:=fun z => hCβge 0 (by norm_num) z
      bR:=bR,bR_pos:=hbRpos,bR_lt:=hbR
      M₀:=M₀,M₀_ge:=hM₀,deriv1:=hM1,deriv2:=hM2
      δ:=δ,δ_pos:=hδpos,δ_lt_half:=hδhalf,δ_lt:=hδsmall
      N:=N,N_gt_one:=hN1,N_gt_sq:=hNsq,N_gt_lin:=hNlin,Hm:=Hm,Hm_close:=hHm }
  exact ⟨D,hBmin,hδε,hBlarge,rfl,hbRε⟩

end SymplecticPacking.General.Compile
