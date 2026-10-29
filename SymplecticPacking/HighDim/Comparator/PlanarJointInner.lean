import SymplecticPacking.HighDim.Comparator.PlanarJointMorse
import SymplecticPacking.HighDim.Comparator.PlanarJointExtension
import SymplecticPacking.HighDim.Comparator.PlanarInnerFamily
import SymplecticPacking.HighDim.Comparator.PlanarCutoffBounds

/-!
# Joint parameter dependence of the planar inner family

The public conclusions are `slice_ordPath_joint` and `slice_ordinary`. The open set
`sliceGood` consists of strict finite coefficient envelopes; `sliceGood_of_box` puts
the original closed parameter box inside it using the explicit extra unit of slack.

The bounded Morse coordinates are kept unchanged. For `slice_fs_joint` only, a local
positive constant-tail density supplies a proper auxiliary area inverse. The area gate
and `DensityExtension.normalize_local` identify that auxiliary normalization with the
original one on the entire source disc. The chart, clock and five explicit segments
then give joint smoothness in every moment parameter, time and source coordinate.
-/

noncomputable section
set_option maxHeartbeats 800000
namespace SymplecticPacking.HighDim.PlanarGen
open Set Filter Topology Complex
open OAI.PackingSufficiencySupport.MomentPolytope (Moments)
open scoped ContDiff Real

variable {m q : ℕ} (Δ : Polytope m q) {F : PolyFn m} (hF : F ≠ []) (j : Fin m)
    {ell : Moments m → ℝ} (hell : ContDiff ℝ ∞ ell) (Lν : Fin q → Moments m → ℝ)
    {R η₀ ξ : ℝ} (hR : 0 ≤ R) (hξ : 0 < ξ)
local notation "D" => sliceInput Δ F j ell Lν R η₀ ξ
include hF hell hR hξ

/-- Open strict envelopes for the finite affine list. -/
def sliceGood (Δ : Polytope m q) (j : Fin m) (ell : Moments m → ℝ)
    (Lν : Fin q → Moments m → ℝ) (R η₀ ξ : ℝ) {F : PolyFn m} : Set (Moments m) := {y | ∀ a ∈ F,
  |a.coef j * ell y| < (sliceInput Δ F j ell Lν R η₀ ξ).L ∧
    |a.eval (Function.update y j 0)| + |a.coef j * ell y| <
      (sliceInput Δ F j ell Lν R η₀ ξ).M}

lemma sliceGood_open : IsOpen (sliceGood Δ j ell Lν R η₀ ξ (F := F)) := by
  classical
  have he : sliceGood Δ j ell Lν R η₀ ξ (F := F) = ⋂ a ∈ F.toFinset,
      {y | |a.coef j * ell y| < (D).L ∧
        |a.eval (Function.update y j 0)| + |a.coef j * ell y| < (D).M} := by
    ext y
    simp [sliceGood]
  rw [he]
  apply isOpen_biInter_finset
  intro a ha
  have hc : Continuous (fun y : Moments m => a.eval (Function.update y j 0)) :=
    (PolyFn.affine_continuous a).comp (by fun_prop)
  exact (isOpen_lt (continuous_const.mul hell.continuous).abs continuous_const).inter
    (isOpen_lt (hc.abs.add (continuous_const.mul hell.continuous).abs) continuous_const)

lemma sliceGood_bounds {y : Moments m} (hy : y ∈ sliceGood Δ j ell Lν R η₀ ξ (F := F)) :
    (∀ p ∈ (D).pieces y, |p.2| ≤ (D).L) ∧
      (∀ p ∈ (D).pieces y, |p.1| + |p.2| ≤ (D).M) := by
  constructor <;> intro p hp <;> obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
  · exact (hy a ha).1.le
  · exact (hy a ha).2.le

lemma slice_value_strict_bound (y : Moments m) (hy : ∀ i, |y i| ≤ 4 * R)
    (hell0 : 0 ≤ ell y) (hbound : ell y ≤ lenBound Δ j R) :
    ∀ p ∈ (D).pieces y, |p.1| + |p.2| < (D).M := by
  have hlen : 0 ≤ lenBound Δ j R := hell0.trans hbound
  have hentry (a : AffinePiece m) :
      0 ≤ |a.const| + 4 * R * (∑ i, |a.coef i|) + |a.coef j| * lenBound Δ j R := by
    positivity
  intro p hp
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
  have hyp : ∀ i, |Function.update y j 0 i| ≤ 4 * R := by
    intro i
    by_cases hi : i = j
    · subst i; simp only [Function.update_self, abs_zero]; positivity
    · simpa only [Function.update_of_ne hi] using hy i
  have hsum : |∑ i, a.coef i * Function.update y j 0 i| ≤ 4 * R * ∑ i, |a.coef i| := by
    calc |∑ i, a.coef i * Function.update y j 0 i|
        ≤ ∑ i, |a.coef i * Function.update y j 0 i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |a.coef i| * (4 * R) := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hyp i) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hinter : |a.eval (Function.update y j 0)| ≤ |a.const| + 4 * R * ∑ i, |a.coef i| := by
    unfold AffinePiece.eval
    exact (abs_add_le _ _).trans (by linarith)
  have hslope : |a.coef j * ell y| ≤ |a.coef j| * lenBound Δ j R := by
    rw [abs_mul, abs_of_nonneg hell0]
    exact mul_le_mul_of_nonneg_left hbound (abs_nonneg _)
  have hs := List.single_le_sum (l := F.map fun b =>
      |b.const| + 4 * R * (∑ i, |b.coef i|) + |b.coef j| * lenBound Δ j R)
    (fun x hx => by obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx; exact hentry b)
    _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
  change |a.eval (Function.update y j 0)| + |a.coef j * ell y| <
    (F.map fun b => |b.const| + 4 * R * (∑ i, |b.coef i|) + |b.coef j| * lenBound Δ j R).sum + 1
  linarith


/-- The original box and length bounds lie strictly inside both finite envelopes. -/
theorem sliceGood_of_box {y : Moments m} (hy : ∀ i, |y i| ≤ 4 * R)
    (hell0 : 0 ≤ ell y) (hbound : ell y ≤ lenBound Δ j R) :
    y ∈ sliceGood Δ j ell Lν R η₀ ξ (F := F) := by
  intro a ha
  have hp : (a.eval (Function.update y j 0), a.coef j * ell y) ∈ (D).pieces y :=
    List.mem_map.mpr ⟨a, ha, rfl⟩
  exact ⟨sliceInput_slope_strict_bound Δ F j ell Lν R η₀ ξ y hell0 hbound _ hp,
    slice_value_strict_bound (η₀ := η₀) Δ hF j hell Lν hR hξ y hy hell0 hbound _ hp⟩

lemma slice_a0_smooth : ContDiff ℝ ∞ (D).a0 := by
  have ha := sliceInput_alphaU_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ
  have hapos := slice_alphaU_pos (η₀ := η₀) Δ hF j hell Lν hR hξ
  exact (contDiff_const.div ha (fun y => (hapos y).ne')).sqrt
    (fun y => (div_pos two_pos (hapos y)).ne')

lemma slice_j0_smooth : ContDiff ℝ ∞ (D).j0 := (slice_a0_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ).mul contDiff_const

lemma slice_XU_deriv_joint : ContDiffOn ℝ ∞ (fun p : Moments m × ℝ => deriv ((D).XU p.1) p.2)
    (sliceGood Δ j ell Lν R η₀ ξ (F := F) ×ˢ univ) := by
  have ho := sliceGood_open (η₀ := η₀) Δ hF j hell Lν hR hξ
  apply partial_deriv_smooth ho
  apply slice_XU_joint_on (η₀ := η₀) Δ hF j hell Lν hR hξ ho
  exact fun y hy => (sliceGood_bounds (η₀ := η₀) Δ hF j hell Lν hR hξ hy).1

/-- The angular well and the uniform modification width depend only on the fixed constants. -/
lemma slice_constants_basic : 0 < (D).epsU ∧ 0 < (D).alphaMin ∧ (D).wellV.Hyp := by
  have hL : 0 ≤ (D).L := sliceInput_L_nonneg Δ F j ell Lν hR η₀ ξ
  let E : Input m := { (D) with pieces := fun _ => [(0, 0)] }
  have hn : E.pieces (0 : Moments m) ≠ [] := by simp [E]
  have hb : ∀ p ∈ E.pieces (0 : Moments m), |p.2| ≤ E.L := by
    intro p hp
    simp only [E, List.mem_singleton] at hp
    subst p
    simpa using hL
  refine ⟨E.epsU_pos (0 : Moments m) hξ hL hn hb, ?_, E.wellV_hyp (0 : Moments m) hξ hL hn hb⟩
  change 0 < 32 * (D).kappa
  exact mul_pos (by norm_num) (Input.kappa_pos hξ hL)

lemma slice_Js_joint : ContDiffOn ℝ ∞
    (fun p : (Moments m × ℝ) × ℂ => (D).Js p.1.1 p.1.2 p.2)
    ((sliceGood Δ j ell Lν R η₀ ξ (F := F) ×ˢ univ) ×ˢ univ) := by
  let Y := sliceGood Δ j ell Lν R η₀ ξ (F := F)
  have hu := slice_XU_deriv_joint (η₀ := η₀) Δ hF j hell Lν hR hξ
  have hx : ContDiffOn ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => deriv ((D).XU p.1.1) p.2.re)
      ((Y ×ˢ univ) ×ˢ univ) :=
    hu.comp (((contDiff_fst.comp contDiff_fst).prodMk (reCLM.contDiff.comp contDiff_snd)).contDiffOn)
      (fun p hp => ⟨hp.1.1, mem_univ _⟩)
  have hL : 0 ≤ (D).L := sliceInput_L_nonneg Δ F j ell Lν hR η₀ ξ
  have hV : ContDiff ℝ ∞ (deriv (D).XV) :=
    (contDiff_infty_iff_deriv.mp (Branch2.Planar.Well.X_smooth
      (slice_constants_basic (η₀ := η₀) Δ hF j hell Lν hR hξ).2.2)).2
  have ha : ContDiff ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => (D).a0 p.1.1) :=
    (slice_a0_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ).comp (contDiff_fst.comp contDiff_fst)
  have ht : ContDiff ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => p.1.2) := contDiff_snd.comp contDiff_fst
  exact ((((contDiffOn_const.sub ht.contDiffOn).mul ha.contDiffOn).add (ht.contDiffOn.mul hx))).mul
    (((contDiffOn_const.sub ht.contDiffOn).mul contDiffOn_const).add
      (ht.contDiffOn.mul (hV.comp (imCLM.contDiff.comp contDiff_snd)).contDiffOn))

/-- One positive flat radius works for every parameter in the strict envelope and every time. -/
lemma slice_Js_uniform_flat : ∃ ρ > 0, ∀ y ∈ sliceGood Δ j ell Lν R η₀ ξ (F := F),
    ∀ s (w : ℂ), ‖w‖ ≤ ρ → (D).Js y s w = (D).j0 y := by
  have hc := slice_constants_basic (η₀ := η₀) Δ hF j hell Lν hR hξ
  let ρ := min (Real.sqrt ((D).alphaMin / 2) * (D).epsU) ((D).wellV.lin * (D).wellV.eps)
  have hρ : 0 < ρ := lt_min (mul_pos (Real.sqrt_pos.mpr (div_pos hc.2.1 two_pos)) hc.1)
    (mul_pos (Branch2.Planar.Well.lin_pos hc.2.2) (Branch2.Planar.Well.eps_pos hc.2.2))
  refine ⟨ρ, hρ, ?_⟩
  intro y hy s w hw
  have hL : 0 ≤ (D).L := sliceInput_L_nonneg Δ F j ell Lν hR η₀ ξ
  have hn := sliceInput_pieces_ne_nil Δ hF j ell Lν R η₀ ξ y
  have hb := (sliceGood_bounds (η₀ := η₀) Δ hF j hell Lν hR hξ hy).1
  apply (D).Js_flat y hξ hL hn hb s w
  apply hw.trans
  have ha := (D).alphaU_bounds y hξ hL hn hb
  exact min_le_min (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith :
    (D).alphaMin / 2 ≤ (D).alphaU y / 2)) hc.1.le) le_rfl

lemma slice_Fs_joint : ContDiffOn ℝ ∞
    (fun p : (Moments m × ℝ) × ℂ => (D).Fs p.1.1 p.1.2 p.2)
    ((sliceGood Δ j ell Lν R η₀ ξ (F := F) ×ˢ univ) ×ˢ univ) := by
  let Y := sliceGood Δ j ell Lν R η₀ ξ (F := F)
  have ho := sliceGood_open (η₀ := η₀) Δ hF j hell Lν hR hξ
  have hx0 := slice_XU_joint_on (η₀ := η₀) Δ hF j hell Lν hR hξ ho
    (fun y hy => (sliceGood_bounds (η₀ := η₀) Δ hF j hell Lν hR hξ hy).1)
  have hx : ContDiffOn ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => (D).XU p.1.1 p.2.re)
      ((Y ×ˢ univ) ×ˢ univ) :=
    hx0.comp (((contDiff_fst.comp contDiff_fst).prodMk (reCLM.contDiff.comp contDiff_snd)).contDiffOn)
      (fun p hp => ⟨hp.1.1, mem_univ _⟩)
  have hv : ContDiff ℝ ∞ (D).XV := Branch2.Planar.Well.X_smooth
    (slice_constants_basic (η₀ := η₀) Δ hF j hell Lν hR hξ).2.2
  have ha : ContDiff ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => (D).a0 p.1.1) :=
    (slice_a0_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ).comp (contDiff_fst.comp contDiff_fst)
  have ht : ContDiff ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => p.1.2) := contDiff_snd.comp contDiff_fst
  have hxr : ContDiffOn ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => (D).Xs p.1.1 p.1.2 p.2.re)
      ((Y ×ˢ univ) ×ˢ univ) :=
    ((((contDiffOn_const.sub ht.contDiffOn).mul ha.contDiffOn).mul
      (reCLM.contDiff.comp contDiff_snd).contDiffOn).add (ht.contDiffOn.mul hx))
  have hyi : ContDiffOn ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => (D).Ys p.1.2 p.2.im)
      ((Y ×ˢ univ) ×ˢ univ) :=
    ((((contDiffOn_const.sub ht.contDiffOn).mul contDiffOn_const).mul
      (imCLM.contDiff.comp contDiff_snd).contDiffOn).add
      (ht.contDiffOn.mul (hv.comp (imCLM.contDiff.comp contDiff_snd)).contDiffOn))
  exact (ofRealCLM.contDiff.comp_contDiffOn hxr).add
    ((ofRealCLM.contDiff.comp_contDiffOn hyi).mul contDiffOn_const)

/-- Joint smoothness of the finite-area normalized family in every moment parameter. -/
theorem slice_fs_joint : ContDiffOn ℝ ∞
    (fun p : (Moments m × ℝ) × ℂ => (D).fs p.1.1 p.1.2 p.2)
    ((sliceGood Δ j ell Lν R η₀ ξ (F := F) ×ˢ Icc (0 : ℝ) 1) ×ˢ
      {z : ℂ | Real.pi * ‖z‖ ^ 2 < (D).pdag}) := by
  let Y := sliceGood Δ j ell Lν R η₀ ξ (F := F)
  let U : Set (Moments m × ℝ) := Y ×ˢ univ
  let S : Set ((Moments m × ℝ) × ℂ) := (Y ×ˢ Icc 0 1) ×ˢ
    {z : ℂ | Real.pi * ‖z‖ ^ 2 < (D).pdag}
  let J : (Moments m × ℝ) → ℂ → ℝ := fun p w => (D).Js p.1 p.2 w
  let jb : (Moments m × ℝ) → ℝ := fun p => (D).j0 p.1
  have hY := sliceGood_open (η₀ := η₀) Δ hF j hell Lν hR hξ
  have hU : IsOpen U := hY.prod isOpen_univ
  have hJ : ContDiffOn ℝ ∞ (Function.uncurry J) (U ×ˢ univ) :=
    slice_Js_joint (η₀ := η₀) Δ hF j hell Lν hR hξ
  have hj : ContDiffOn ℝ ∞ jb U :=
    ((slice_j0_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ).comp contDiff_fst).contDiffOn
  obtain ⟨ρ, hρ, hflat⟩ := slice_Js_uniform_flat (η₀ := η₀) Δ hF j hell Lν hR hξ
  have hL : 0 ≤ (D).L := sliceInput_L_nonneg Δ F j ell Lν hR η₀ ξ
  have hn (y : Moments m) := sliceInput_pieces_ne_nil Δ hF j ell Lν R η₀ ξ y
  intro p hp
  have hb := (sliceGood_bounds (η₀ := η₀) Δ hF j hell Lν hR hξ hp.1.1).1
  have hbM := (sliceGood_bounds (η₀ := η₀) Δ hF j hell Lν hR hξ hp.1.1).2
  have hE := (D).Ebar_pos_from_pieces p.1.1 hξ hL (hn p.1.1) hb hbM
  have hrad := Real.sqrt_pos.mpr hE
  obtain ⟨V, hV, hpV, hVU, HK⟩ := JointDensity.extension_hyp hU hJ hj hρ hrad
    (fun q hq w hw => hflat q.1 hq.1 q.2 w hw)
    (show p.1 ∈ U from ⟨hp.1.1, mem_univ _⟩)
    (mul_pos ((D).a0_pos_from_pieces p.1.1 hξ hL (hn p.1.1) hb)
      ((D).b0_pos_of_pieces p.1.1 hξ hL (hn p.1.1) hb))
    ((D).Js_pos p.1.1 hξ hL (hn p.1.1) hb hp.1.2)
  let K := JointDensity.extension J jb (Real.sqrt (D).Ebar)
  let N : (Moments m × ℝ) → ℂ → ℂ := fun q z => Inner.TrotInv (JointDensity.family K q) 0
    (Inner.Darea (JointDensity.family K q) 0 z)
  have hN : ContDiffAt ℝ ∞ (Function.uncurry N) p :=
    (JointDensity.normalize_smooth HK).contDiffAt ((hV.prod isOpen_univ).mem_nhds ⟨hpV, mem_univ _⟩)
  have hFmap : ContDiffAt ℝ ∞ (fun q : (Moments m × ℝ) × ℂ => (D).Fs q.1.1 q.1.2 q.2)
      (p.1, N p.1 p.2) := (slice_Fs_joint (η₀ := η₀) Δ hF j hell Lν hR hξ).contDiffAt
    (((hY.prod isOpen_univ).prod isOpen_univ).mem_nhds
      (show (p.1, N p.1 p.2) ∈ (Y ×ˢ univ) ×ˢ (univ : Set ℂ) from ⟨⟨hp.1.1, mem_univ _⟩, mem_univ _⟩))
  have haux : ContDiffAt ℝ ∞ (fun q : (Moments m × ℝ) × ℂ => (D).Fs q.1.1 q.1.2 (N q.1 q.2)) p := by
    have hmap : ContDiffAt ℝ ∞ (fun q : (Moments m × ℝ) × ℂ => (q.1, N q.1 q.2)) p :=
      contDiffAt_fst.prodMk hN
    exact ContDiffAt.comp p
      (g := fun q : (Moments m × ℝ) × ℂ => (D).Fs q.1.1 q.1.2 q.2)
      (f := fun q : (Moments m × ℝ) × ℂ => (q.1, N q.1 q.2)) hFmap hmap
  have heq : ∀ q ∈ S, q.1 ∈ V → (D).fs q.1.1 q.1.2 q.2 = (D).Fs q.1.1 q.1.2 (N q.1 q.2) := by
    intro q hq hqV
    have hbs := (sliceGood_bounds (η₀ := η₀) Δ hF j hell Lν hR hξ hq.1.1).1
    have hMs := (sliceGood_bounds (η₀ := η₀) Δ hF j hell Lν hR hξ hq.1.1).2
    apply congrArg ((D).Fs q.1.1 q.1.2)
    apply (DensityExtension.normalize_local (JointDensity.scalar_hyp HK hqV)
      (show q.1.2 ∈ Ioo (-1 : ℝ) 2 from ⟨by linarith [hq.1.2.1], by linarith [hq.1.2.2]⟩)
      hrad.le ((D).Js_slice_continuous q.1.1 hξ hL (hn q.1.1) hbs q.1.2)
      ((D).Js_pos q.1.1 hξ hL (hn q.1.1) hbs hq.1.2)
      (fun w hw => (DensityExtension.extend_eq hrad hw).symm) ?_).1
    rw [Real.sq_sqrt hE.le]
    exact hq.2.trans ((D).Ebar_area_gate q.1.1 hξ hL (hn q.1.1) hbs hMs hq.1.2)
  apply haux.contDiffWithinAt.congr_of_eventuallyEq_of_mem (s := S) (hx := hp)
  have hnear : ∀ᶠ q in 𝓝[S] p, q.1 ∈ V :=
    ((continuous_fst.tendsto p).eventually (hV.mem_nhds hpV)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hnear] with q hq hqV
  exact heq q hq hqV

lemma slice_rb_smooth : ContDiff ℝ ∞ (D).rb := by
  have hv := sliceInput_vstar_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ
  exact (hv.div_const Real.pi).sqrt (fun y =>
    (div_pos (slice_critical_spec (η₀ := η₀) Δ hF j hell Lν hR hξ y).1.1 Real.pi_pos).ne')

lemma slice_Clam_joint_at {p : (Moments m × ℝ) × ℂ}
    (hp : 0 < (D).vstar p.1.1 + p.1.2 * p.2.re) :
    ContDiffAt ℝ ∞ (fun q : (Moments m × ℝ) × ℂ => (D).Clam q.1.1 q.1.2 q.2) p := by
  have hv : ContDiff ℝ ∞ (fun q : (Moments m × ℝ) × ℂ => (D).vstar q.1.1) :=
    (sliceInput_vstar_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ).comp (contDiff_fst.comp contDiff_fst)
  have hr : ContDiff ℝ ∞ (fun q : (Moments m × ℝ) × ℂ => (D).rb q.1.1) :=
    (slice_rb_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ).comp (contDiff_fst.comp contDiff_fst)
  have ht : ContDiff ℝ ∞ (fun q : (Moments m × ℝ) × ℂ => q.1.2) := contDiff_snd.comp contDiff_fst
  have hre : ContDiff ℝ ∞ (fun q : (Moments m × ℝ) × ℂ => q.2.re) := reCLM.contDiff.comp contDiff_snd
  have him : ContDiff ℝ ∞ (fun q : (Moments m × ℝ) × ℂ => q.2.im) := imCLM.contDiff.comp contDiff_snd
  have hθ : ContDiff ℝ ∞ (fun q : (Moments m × ℝ) × ℂ => ((2 * Real.pi * q.1.2 * q.2.im : ℝ) : ℂ) * I) :=
    (ofRealCLM.contDiff.comp ((contDiff_const.mul ht).mul him)).mul contDiff_const
  have hHy : ContDiff ℝ ∞ (fun q : (Moments m × ℝ) × ℂ => (D).Hy q.1.1 q.1.2 q.2) :=
    (((ofRealCLM.contDiff.comp (contDiff_const.mul hr)).mul contDiff_const).mul (Qhat.gexp_contDiff.comp hθ))
  have harg : ContDiffAt ℝ ∞ (fun q : (Moments m × ℝ) × ℂ =>
      Real.sqrt (((D).vstar q.1.1 + q.1.2 * q.2.re) / Real.pi)) p :=
    (Real.contDiffAt_sqrt (div_pos hp Real.pi_pos).ne').comp p
      ((hv.add (ht.mul hre)).div_const Real.pi).contDiffAt
  have hrp : 0 < (D).rb p.1.1 := Real.sqrt_pos.mpr
    (div_pos (slice_critical_spec (η₀ := η₀) Δ hF j hell Lν hR hξ p.1.1).1.1 Real.pi_pos)
  have hden : ContDiffAt ℝ ∞ (fun q : (Moments m × ℝ) × ℂ =>
      (Real.pi * ((D).rb q.1.1 + Real.sqrt (((D).vstar q.1.1 + q.1.2 * q.2.re) / Real.pi)))⁻¹) p :=
    (contDiffAt_const.mul (hr.contDiffAt.add harg)).inv (by
      have hh := Real.sqrt_nonneg (((D).vstar p.1.1 + p.1.2 * p.2.re) / Real.pi)
      positivity)
  have hHx : ContDiffAt ℝ ∞ (fun q : (Moments m × ℝ) × ℂ => (D).Hx q.1.1 q.1.2 q.2) p :=
    (ofRealCLM.contDiff.contDiffAt.comp p hden).mul
      ((Complex.contDiff_exp (𝕜 := ℝ)).contDiffAt.comp p hθ.contDiffAt)
  exact ((ofRealCLM.contDiff.comp hr).neg.contDiffAt.sub
    ((ofRealCLM.contDiff.comp him).contDiffAt.mul hHy.contDiffAt)).sub
    ((ofRealCLM.contDiff.comp hre).contDiffAt.mul hHx)

/-- The rescaled inner family is smooth jointly in all parameters. -/
theorem slice_qin_joint : ContDiffOn ℝ ∞
    (fun p : (Moments m × ℝ) × ℂ => (D).qin p.1.1 p.1.2 p.2)
    ((sliceGood Δ j ell Lν R η₀ ξ (F := F) ×ˢ Icc (0 : ℝ) 1) ×ˢ
      {z : ℂ | Real.pi * ‖z‖ ^ 2 < (D).pdag}) := by
  intro p hp
  have hbs := (sliceGood_bounds (η₀ := η₀) Δ hF j hell Lν hR hξ hp.1.1).1
  have hMs := (sliceGood_bounds (η₀ := η₀) Δ hF j hell Lν hR hξ hp.1.1).2
  have hn := sliceInput_pieces_ne_nil Δ hF j ell Lν R η₀ ξ p.1.1
  have hL : 0 ≤ (D).L := sliceInput_L_nonneg Δ F j ell Lν hR η₀ ξ
  have hl := (D).lam_smooth p.1.1 hξ hL hn hbs hMs
  have hdom := ((D).qin_chart_domain p.1.1 hξ hL hn hbs hMs hp.1.2 hp.2).1
  have hC := slice_Clam_joint_at (η₀ := η₀) Δ hF j hell Lν hR hξ
    (p := ((p.1.1, (D).lam p.1.2), (D).fs p.1.1 p.1.2 p.2)) hdom
  have hfs := slice_fs_joint (η₀ := η₀) Δ hF j hell Lν hR hξ p hp
  have hmap : ContDiffWithinAt ℝ ∞ (fun q : (Moments m × ℝ) × ℂ =>
      ((q.1.1, (D).lam q.1.2), (D).fs q.1.1 q.1.2 q.2))
      ((sliceGood Δ j ell Lν R η₀ ξ (F := F) ×ˢ Icc (0 : ℝ) 1) ×ˢ
        {z : ℂ | Real.pi * ‖z‖ ^ 2 < (D).pdag}) p :=
    (contDiffWithinAt_fst.fst.prodMk
      ((hl.comp (contDiff_snd.comp contDiff_fst)).contDiffAt.contDiffWithinAt)).prodMk hfs
  exact hC.comp_contDiffWithinAt p hmap

lemma slice_b0_pos : 0 < (D).b0 := one_div_pos.mpr
  (Branch2.Planar.Well.lin_pos (slice_constants_basic (η₀ := η₀) Δ hF j hell Lν hR hξ).2.2)

lemma slice_j0_pos (y : Moments m) : 0 < (D).j0 y := by
  have ha := slice_alphaU_pos (η₀ := η₀) Δ hF j hell Lν hR hξ y
  have hb := slice_b0_pos (η₀ := η₀) Δ hF j hell Lν hR hξ
  exact mul_pos (Real.sqrt_pos.mpr (div_pos two_pos ha)) hb

lemma slice_cx_smooth : ContDiff ℝ ∞ (D).cx := by
  have hj := slice_j0_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ
  have hp := slice_j0_pos (η₀ := η₀) Δ hF j hell Lν hR hξ
  exact (slice_a0_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ).div
    (hj.sqrt (fun y => (hp y).ne')) (fun y => (Real.sqrt_pos.mpr (hp y)).ne')

lemma slice_cy_smooth : ContDiff ℝ ∞ (D).cy := by
  have hj := slice_j0_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ
  have hp := slice_j0_pos (η₀ := η₀) Δ hF j hell Lν hR hξ
  exact contDiff_const.div (hj.sqrt (fun y => (hp y).ne'))
    (fun y => (Real.sqrt_pos.mpr (hp y)).ne')

lemma slice_rb_pos (y : Moments m) : 0 < (D).rb y := Real.sqrt_pos.mpr
  (div_pos (slice_critical_spec (η₀ := η₀) Δ hF j hell Lν hR hξ y).1.1 Real.pi_pos)

lemma slice_A11_smooth : ContDiff ℝ ∞ (D).A11 := by
  have hr := slice_rb_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ
  exact ((slice_cx_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ).div (contDiff_const.mul hr)
    (fun y => (mul_pos (mul_pos two_pos Real.pi_pos)
      (slice_rb_pos (η₀ := η₀) Δ hF j hell Lν hR hξ y)).ne')).neg

lemma slice_A22_smooth : ContDiff ℝ ∞ (D).A22 :=
  (((contDiff_const.mul (slice_rb_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ)).mul
    (slice_cy_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ))).neg

lemma slice_A11_neg (y : Moments m) : (D).A11 y < 0 := by
  have hj := slice_j0_pos (η₀ := η₀) Δ hF j hell Lν hR hξ y
  have ha := slice_alphaU_pos (η₀ := η₀) Δ hF j hell Lν hR hξ y
  have hr := slice_rb_pos (η₀ := η₀) Δ hF j hell Lν hR hξ y
  unfold Input.A11 Input.cx Input.a0
  apply neg_neg_of_pos
  positivity

lemma slice_A22_neg (y : Moments m) : (D).A22 y < 0 := by
  have hj := slice_j0_pos (η₀ := η₀) Δ hF j hell Lν hR hξ y
  have hb := slice_b0_pos (η₀ := η₀) Δ hF j hell Lν hR hξ
  have hr := slice_rb_pos (η₀ := η₀) Δ hF j hell Lν hR hξ y
  unfold Input.A22 Input.cy
  apply neg_neg_of_pos
  positivity

lemma slice_bpt_smooth : ContDiff ℝ ∞ (D).bpt :=
  (ofRealCLM.contDiff.comp (slice_rb_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ)).neg

lemma slice_A0_joint : ContDiff ℝ ∞ (fun p : Moments m × ℂ => (D).A0 p.1 p.2) := by
  have h1 := ((slice_A11_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ).comp contDiff_fst).mul
    (reCLM.contDiff.comp contDiff_snd)
  have h2 := ((slice_A22_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ).comp contDiff_fst).mul
    (imCLM.contDiff.comp contDiff_snd)
  exact (ofRealCLM.contDiff.comp h1).add ((ofRealCLM.contDiff.comp h2).mul contDiff_const)

lemma slice_Msig_joint : ContDiff ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => (D).Msig p.1.1 p.1.2 p.2) := by
  have ha : ContDiff ℝ ∞ (fun y => |(D).A11 y|) := by
    have heq : (fun y : Moments m => |(D).A11 y|) = (fun y => -(D).A11 y) :=
      funext fun y => abs_of_neg (slice_A11_neg (η₀ := η₀) Δ hF j hell Lν hR hξ y)
    rw [heq]
    exact (slice_A11_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ).neg
  have hb : ContDiff ℝ ∞ (fun y => |(D).A22 y|) := by
    have heq : (fun y : Moments m => |(D).A22 y|) = (fun y => -(D).A22 y) :=
      funext fun y => abs_of_neg (slice_A22_neg (η₀ := η₀) Δ hF j hell Lν hR hξ y)
    rw [heq]
    exact (slice_A22_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ).neg
  have hy : ContDiff ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => p.1.1) := contDiff_fst.comp contDiff_fst
  have ht : ContDiff ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => p.1.2) := contDiff_snd.comp contDiff_fst
  have hr1 := (ha.comp hy).rpow ht (fun p =>
    (abs_pos.mpr (slice_A11_neg (η₀ := η₀) Δ hF j hell Lν hR hξ p.1.1).ne).ne')
  have hr2 := (hb.comp hy).rpow ht (fun p =>
    (abs_pos.mpr (slice_A22_neg (η₀ := η₀) Δ hF j hell Lν hR hξ p.1.1).ne).ne')
  have hlin : ContDiff ℝ ∞ (fun p : (Moments m × ℝ) × ℂ =>
      ((|(D).A11 p.1.1| ^ p.1.2 * p.2.re : ℝ) : ℂ) +
        ((|(D).A22 p.1.1| ^ p.1.2 * p.2.im : ℝ) : ℂ) * I) :=
    (ofRealCLM.contDiff.comp (hr1.mul (reCLM.contDiff.comp contDiff_snd))).add
      ((ofRealCLM.contDiff.comp (hr2.mul (imCLM.contDiff.comp contDiff_snd))).mul contDiff_const)
  exact Inner.contDiff_Rot.comp ((contDiff_const.mul ht).prodMk hlin)

/-- Every parameter in the open envelope gives the same ordinary-path contract. -/
theorem slice_ordinary {y : Moments m} (hy : y ∈ sliceGood Δ j ell Lν R η₀ ξ (F := F)) :
    Qhat.OrdinaryPath ((D).pathData y) := by
  have hn := sliceInput_pieces_ne_nil Δ hF j ell Lν R η₀ ξ y
  have hL : 0 ≤ (D).L := sliceInput_L_nonneg Δ F j ell Lν hR η₀ ξ
  have hb := sliceGood_bounds (η₀ := η₀) Δ hF j hell Lν hR hξ hy
  exact (D).ordinary_of_pieces y hξ hL hn hb.1 hb.2

/-- The five-segment ordinary path is smooth jointly in all moment parameters. -/
theorem slice_ordPath_joint : ContDiffOn ℝ ∞
    (fun p : (Moments m × ℝ) × ℂ => (D).ordPath p.1.1 p.1.2 p.2)
    ((sliceGood Δ j ell Lν R η₀ ξ (F := F) ×ˢ univ) ×ˢ
      {z : ℂ | Real.pi * ‖z‖ ^ 2 < (D).pdag}) := by
  let Y := sliceGood Δ j ell Lν R η₀ ξ (F := F)
  let T : Set ((Moments m × ℝ) × ℂ) := (Y ×ˢ univ) ×ˢ
    {z : ℂ | Real.pi * ‖z‖ ^ 2 < (D).pdag}
  intro p hp
  have hL : 0 ≤ (D).L := sliceInput_L_nonneg Δ F j ell Lν hR η₀ ξ
  have hn := sliceInput_pieces_ne_nil Δ hF j ell Lν R η₀ ξ p.1.1
  have hb := (sliceGood_bounds (η₀ := η₀) Δ hF j hell Lν hR hξ hp.1.1).1
  have hM := (sliceGood_bounds (η₀ := η₀) Δ hF j hell Lν hR hξ hp.1.1).2
  have hc := ((D).ordinary_of_pieces p.1.1 hξ hL hn hb hM).c_pos
  have ht : ContDiff ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => p.1.2) := contDiff_snd.comp contDiff_fst
  have hy : ContDiff ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => p.1.1) := contDiff_fst.comp contDiff_fst
  have hz : ContDiff ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => p.2) := contDiff_snd
  have hk (n : ℕ) : ContDiff ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => Input.clock n p.1.2) :=
    (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).comp ht
  have hq3 : ContDiffOn ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => (D).qin p.1.1 (Input.clock 3 p.1.2) p.2) T :=
    (slice_qin_joint (η₀ := η₀) Δ hF j hell Lν hR hξ).comp
      (((hy.prodMk (hk 3)).prodMk hz).contDiffOn) (fun p hp =>
        ⟨⟨hp.1.1, ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩⟩, hp.2⟩)
  have hq1 : ContDiffOn ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => (D).qin p.1.1 1 p.2) T :=
    (slice_qin_joint (η₀ := η₀) Δ hF j hell Lν hR hξ).comp
      (((hy.prodMk contDiff_const).prodMk hz).contDiffOn)
      (fun p hp => ⟨⟨hp.1.1, ⟨zero_le_one, le_rfl⟩⟩, hp.2⟩)
  have hbpt := (slice_bpt_smooth (η₀ := η₀) Δ hF j hell Lν hR hξ).comp hy
  have hA := (slice_A0_joint (η₀ := η₀) Δ hF j hell Lν hR hξ).comp (hy.prodMk hz)
  have hMs := (slice_Msig_joint (η₀ := η₀) Δ hF j hell Lν hR hξ).comp ((hy.prodMk (hk 2)).prodMk hz)
  have hp0 : ContDiff ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => (D).cnew ^ Input.clock 0 p.1.2) :=
    contDiff_const.rpow (hk 0) (fun _ => hc.ne')
  have hp4 : ContDiff ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => (D).cnew ^ (1 - Input.clock 4 p.1.2)) :=
    contDiff_const.rpow (contDiff_const.sub (hk 4)) (fun _ => hc.ne')
  have hfirst := ((ofRealCLM.contDiff.comp hp0).mul hz).contDiffOn (s := T)
  have hsecond := ((ofRealCLM.contDiff.comp (hk 1)).mul hbpt).contDiffOn (s := T)
  have hthird := (contDiffOn_const (c := ((D).cnew : ℂ))).mul ((hMs.sub hz).contDiffOn (s := T))
  have hfourth := (contDiffOn_const (c := ((D).cnew : ℂ))).mul ((hq3.sub hbpt.contDiffOn).sub hA.contDiffOn)
  have hfifth := ((ofRealCLM.contDiff.comp (hp4.sub (contDiff_const (c := (D).cnew)))).contDiffOn).mul (hq1.sub hbpt.contDiffOn)
  have hall : ContDiffOn ℝ ∞ (fun p : (Moments m × ℝ) × ℂ => (D).ordPath p.1.1 p.1.2 p.2) T :=
    (((hfirst.add hsecond).add hthird).add hfourth).add hfifth
  exact hall p hp

end SymplecticPacking.HighDim.PlanarGen
