import SymplecticPacking.HighDim.Comparator.Rearrangement

/-!
# The finite comparator (paper prop:cmp-fixed-point; supplement S-prop:fcp-fixed-point)

Data: a polytope `Δ`, a continuous concave profile `P` with positive mean `μ`, a dilation factor
`τ < 1` and `β > 0` with `P ≥ β` on `Δ ∖ τΔ`, and a gap parameter `0 < d < min(μ, β)`.
With `q = (1−τ)(μ−d)`, `B = max(1, d − min P + 1)`, `λ = 1 − q/(2(B+q))` the iterates
`K_0 = 0`, `K_{r+1} = ℛ(λ K_r − P)` converge geometrically to the fixed point `K_λ`, which
satisfies `(1−λ)K_λ < −d`. For the explicit `N` below, `ℛ(K_N − P) ≤ K_N − 7d/8` on `Δ`.
Source: OpenAI preprint §2.2 (contraction argument).
-/

noncomputable section

namespace SymplecticPacking.HighDim

open Set MeasureTheory
open OAI.PackingSufficiencySupport.MomentPolytope (Moments region)

variable {m q : ℕ}

/-- Input of the comparator. -/
structure CmpInput (m q : ℕ) where
  Δ : Polytope m q
  P : Moments m → ℝ
  τ : ℝ
  β : ℝ
  d : ℝ

namespace CmpInput

variable (I : CmpInput m q)

/-- Mean of `P` over `Δ`. -/
def mean : ℝ := (∫ p in I.Δ.set, I.P p) / (volume I.Δ.set).toReal

/-- Minimum of `P` over `Δ`. -/
def pmin : ℝ := sInf (I.P '' I.Δ.set)

/-- `‖P‖_∞` over `Δ`. -/
def pnorm : ℝ := sSup ((fun p => |I.P p|) '' I.Δ.set)

/-- `q = (1 − τ)(μ − d)`. -/
def qq : ℝ := (1 - I.τ) * (I.mean - I.d)

/-- `B = max(1, d − min P + 1)`. -/
def bigB : ℝ := max 1 (I.d - I.pmin + 1)

/-- The contraction factor `λ = 1 − q/(2(B+q))`. -/
def lam : ℝ := 1 - I.qq / (2 * (I.bigB + I.qq))

/-- The iterates `K_0 = 0`, `K_{r+1} = ℛ(λ K_r − P)`. -/
def Kiter : ℕ → Moments m → ℝ
  | 0 => fun _ => 0
  | r + 1 => rearrAll I.Δ (fun p => I.lam * Kiter r p - I.P p)

/-- The explicit iteration count: `λ^N ‖P‖/(1−λ) < d/16` holds by Bernoulli's inequality
`λ^{-N} ≥ 1 + N(λ^{-1} − 1)` as soon as `1 + N(λ^{-1}−1) > 16‖P‖/(d(1−λ))`. -/
def Nfix : ℕ :=
  ⌈(16 * I.pnorm / (I.d * (1 - I.lam))) / (I.lam⁻¹ - 1)⌉₊ + 1

/-- The comparator `K_N`. -/
def Kfin : Moments m → ℝ := I.Kiter I.Nfix

/-- Hypotheses of prop:cmp-fixed-point. -/
structure Spec : Prop where
  Δ_spec : I.Δ.Spec
  P_cont : ContinuousOn I.P I.Δ.set
  P_concave : ConcaveOn ℝ I.Δ.set I.P
  vol_pos : 0 < (volume I.Δ.set).toReal
  τ_pos : 0 < I.τ
  τ_lt : I.τ < 1
  outer : ∀ p ∈ I.Δ.set, p ∉ (I.Δ.dilate I.τ).set → I.β ≤ I.P p
  d_pos : 0 < I.d
  d_lt_mean : I.d < I.mean
  d_lt_β : I.d < I.β

variable {I}

theorem qq_pos (hI : I.Spec) : 0 < I.qq :=
  mul_pos (by linarith [hI.τ_lt]) (by linarith [hI.d_lt_mean])

theorem one_le_bigB : 1 ≤ I.bigB := le_max_left _ _

theorem lam_mem (hI : I.Spec) : 1 / 2 < I.lam ∧ I.lam < 1 := by
  have hq := qq_pos hI
  have hB := I.one_le_bigB
  have hden : 0 < 2 * (I.bigB + I.qq) := by linarith
  have h1 : 0 < I.qq / (2 * (I.bigB + I.qq)) := div_pos hq hden
  have h2 : I.qq / (2 * (I.bigB + I.qq)) < 1 / 2 := by
    rw [div_lt_iff₀ hden]; linarith
  simp only [lam]
  constructor <;> linarith

theorem Kiter_convexCont (hI : I.Spec) (r : ℕ) : ConvexCont I.Δ (I.Kiter r) := by
  induction r with
  | zero => exact ⟨continuousOn_const, convexOn_const _ I.Δ.convex_set⟩
  | succ r ih =>
    have hl : 0 ≤ I.lam := (lt_trans (by norm_num) (lam_mem hI).1).le
    refine rearrAll_convexCont hI.Δ_spec ⟨(ih.1.const_smul I.lam).sub hI.P_cont, ?_⟩
    exact (ih.2.smul hl).sub hI.P_concave

/-! ### Proof of the finite comparator gap

We avoid the fixed point `K_λ`: `K_N` is an approximate fixed point,
`|ℛ(λK_N − P) − K_N| ≤ λ^N ‖P‖`, its integral is exactly `−(∫P)(1 − λ^N)/(1 − λ)`, and the
max/convexity contradiction runs with the slack `B ≥ 1`. -/

/-- The step function `F_r = λ K_r − P` is continuous and convex. -/
theorem Fstep_convexCont (hI : I.Spec) (r : ℕ) :
    ConvexCont I.Δ (fun p => I.lam * I.Kiter r p - I.P p) := by
  have hl : 0 ≤ I.lam := (lt_trans (by norm_num) (lam_mem hI).1).le
  have ih := Kiter_convexCont hI r
  exact ⟨(ih.1.const_smul I.lam).sub hI.P_cont, (ih.2.smul hl).sub hI.P_concave⟩

theorem convexCont_add_const' {Δ : Polytope m q} {F : Moments m → ℝ} (hF : ConvexCont Δ F)
    (c : ℝ) : ConvexCont Δ (fun x => F x + c) :=
  ⟨hF.1.add continuousOn_const, hF.2.add_const c⟩

/-- `ℛ` is `1`-Lipschitz from above: `F ≤ G + c` implies `ℛF ≤ ℛG + c`. -/
theorem rearrAll_shift {Δ : Polytope m q} (hΔ : Δ.Spec) {F G : Moments m → ℝ}
    (hF : ConvexCont Δ F) (hG : ConvexCont Δ G) {c : ℝ} (h : ∀ p ∈ Δ.set, F p ≤ G p + c) :
    ∀ p ∈ Δ.set, rearrAll Δ F p ≤ rearrAll Δ G p + c := by
  intro p hp
  have := rearrAll_mono hΔ hF (convexCont_add_const' hG c) h p hp
  rwa [rearrAll_add_const hΔ hG c hp] at this

theorem rearrList_zero {Δ : Polytope m q} (l : List (Fin m)) :
    rearrList Δ l (fun _ => 0) = fun _ => 0 := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have h0 : rearr Δ j (fun _ => (0 : ℝ)) = fun _ => 0 := by
      funext p; simp [rearr]
    change rearrList Δ l (rearr Δ j (fun _ => 0)) = _
    rw [h0, ih]

theorem rearrAll_zero {Δ : Polytope m q} (p : Moments m) : rearrAll Δ (fun _ => 0) p = 0 := by
  rw [rearrAll_eq, rearrList_zero]

theorem zero_mem_set {Δ : Polytope m q} (hΔ : Δ.Spec) : (0 : Moments m) ∈ Δ.set := by
  refine ⟨fun j => le_rfl, fun ν => ?_⟩
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  exact (hΔ.ℓ_pos ν).le

theorem P_abs_le (hI : I.Spec) : ∀ p ∈ I.Δ.set, |I.P p| ≤ I.pnorm := by
  intro p hp
  have hb : BddAbove ((fun x => |I.P x|) '' I.Δ.set) :=
    hI.Δ_spec.compact.bddAbove_image (continuous_abs.comp_continuousOn hI.P_cont)
  exact le_csSup hb ⟨p, hp, rfl⟩

theorem pmin_le (hI : I.Spec) : ∀ p ∈ I.Δ.set, I.pmin ≤ I.P p := fun p hp =>
  csInf_le (hI.Δ_spec.compact.bddBelow_image hI.P_cont) ⟨p, hp, rfl⟩

theorem pnorm_nonneg : 0 ≤ I.pnorm :=
  Real.sSup_nonneg (by rintro _ ⟨x, -, rfl⟩; exact abs_nonneg _)

/-- Successive iterates differ by at most `λ^r ‖P‖` on `Δ`. -/
theorem Kiter_step (hI : I.Spec) (r : ℕ) :
    ∀ p ∈ I.Δ.set, |I.Kiter (r + 1) p - I.Kiter r p| ≤ I.lam ^ r * I.pnorm := by
  have hΔ := hI.Δ_spec
  have hl0 : 0 ≤ I.lam := (lt_trans (by norm_num) (lam_mem hI).1).le
  induction r with
  | zero =>
    intro p hp
    have hK0 : ∀ x, I.Kiter 0 x = 0 := fun _ => rfl
    have hup := rearrAll_le_sup hΔ (Fstep_convexCont hI 0) (M := I.pnorm) (fun x hx => by
      show I.lam * I.Kiter 0 x - I.P x ≤ I.pnorm
      rw [hK0]; linarith [(abs_le.1 (P_abs_le hI x hx)).1]) p hp
    have hlo := rearrAll_shift hΔ (F := fun _ => 0)
      ⟨continuousOn_const, convexOn_const _ I.Δ.convex_set⟩ (Fstep_convexCont hI 0)
      (c := I.pnorm) (fun x hx => by
        show (0 : ℝ) ≤ I.lam * I.Kiter 0 x - I.P x + I.pnorm
        rw [hK0]; linarith [(abs_le.1 (P_abs_le hI x hx)).2]) p hp
    rw [rearrAll_zero] at hlo
    change |rearrAll I.Δ (fun p => I.lam * I.Kiter 0 p - I.P p) p - 0| ≤ I.lam ^ 0 * I.pnorm
    rw [pow_zero, one_mul, sub_zero, abs_le]
    constructor <;> linarith
  | succ r ih =>
    intro p hp
    have h1 : ∀ x ∈ I.Δ.set, I.lam * I.Kiter (r + 1) x - I.P x ≤
        (I.lam * I.Kiter r x - I.P x) + I.lam ^ (r + 1) * I.pnorm := by
      intro x hx
      have := mul_le_mul_of_nonneg_left (abs_le.1 (ih x hx)).2 hl0
      rw [pow_succ]; nlinarith
    have h2 : ∀ x ∈ I.Δ.set, I.lam * I.Kiter r x - I.P x ≤
        (I.lam * I.Kiter (r + 1) x - I.P x) + I.lam ^ (r + 1) * I.pnorm := by
      intro x hx
      have := mul_le_mul_of_nonneg_left (abs_le.1 (ih x hx)).1 hl0
      rw [pow_succ]; nlinarith
    have hu := rearrAll_shift hΔ (Fstep_convexCont hI (r + 1)) (Fstep_convexCont hI r) h1 p hp
    have hd := rearrAll_shift hΔ (Fstep_convexCont hI r) (Fstep_convexCont hI (r + 1)) h2 p hp
    change |rearrAll I.Δ (fun p => I.lam * I.Kiter (r + 1) p - I.P p) p -
      rearrAll I.Δ (fun p => I.lam * I.Kiter r p - I.P p) p| ≤ _
    rw [abs_le]; constructor <;> linarith

/-- Exact integral of the iterates: `(∫K_r)(1 − λ) = −(∫P)(1 − λ^r)`. -/
theorem Kiter_integral (hI : I.Spec) (r : ℕ) :
    (∫ p in I.Δ.set, I.Kiter r p) * (1 - I.lam) =
      -(∫ p in I.Δ.set, I.P p) * (1 - I.lam ^ r) := by
  induction r with
  | zero => simp [Kiter]
  | succ r ih =>
    have hK := Kiter_convexCont hI r
    have hint : ∫ p in I.Δ.set, I.Kiter (r + 1) p =
        I.lam * (∫ p in I.Δ.set, I.Kiter r p) - ∫ p in I.Δ.set, I.P p := by
      change ∫ p in I.Δ.set, rearrAll I.Δ (fun p => I.lam * I.Kiter r p - I.P p) p = _
      rw [rearrAll_integral hI.Δ_spec (Fstep_convexCont hI r)]
      rw [integral_sub, integral_const_mul]
      · exact (hK.1.integrableOn_compact hI.Δ_spec.compact).const_mul _
      · exact hI.P_cont.integrableOn_compact hI.Δ_spec.compact
    rw [hint, pow_succ]
    linear_combination I.lam * ih

theorem integral_P_eq (hI : I.Spec) :
    ∫ p in I.Δ.set, I.P p = I.mean * (volume I.Δ.set).toReal := by
  unfold mean
  field_simp [hI.vol_pos.ne']

theorem mean_le_pnorm (hI : I.Spec) : I.mean ≤ I.pnorm := by
  have hΔ := hI.Δ_spec
  have h := setIntegral_mono_on (μ := volume) (hI.P_cont.integrableOn_compact hΔ.compact)
    ((continuousOn_const (c := I.pnorm)).integrableOn_compact hΔ.compact)
    hΔ.compact.isClosed.measurableSet
    (fun x hx => (le_abs_self _).trans (P_abs_le hI x hx))
  rw [setIntegral_const, smul_eq_mul, measureReal_def] at h
  unfold mean
  rw [div_le_iff₀ hI.vol_pos]
  linarith

/-- The value at the origin (the minimum) is at most the mean. -/
theorem Kiter_origin (hI : I.Spec) (r : ℕ) :
    (1 - I.lam) * I.Kiter (r + 1) 0 ≤ -I.mean * (1 - I.lam ^ (r + 1)) := by
  have hΔ := hI.Δ_spec
  have hs : 0 < 1 - I.lam := by linarith [(lam_mem hI).2]
  have hV := hI.vol_pos
  have h0 := zero_mem_set hΔ
  have hK := Kiter_convexCont hI (r + 1)
  have hmono : ∀ x ∈ I.Δ.set, I.Kiter (r + 1) 0 ≤ I.Kiter (r + 1) x := fun x hx =>
    rearrAll_monotone hΔ (Fstep_convexCont hI r) 0 h0 x hx (fun j => hx.1 j)
  have h := setIntegral_mono_on (μ := volume)
    ((continuousOn_const (c := I.Kiter (r + 1) 0)).integrableOn_compact hΔ.compact)
    (hK.1.integrableOn_compact hΔ.compact) hΔ.compact.isClosed.measurableSet hmono
  rw [setIntegral_const, smul_eq_mul, measureReal_def] at h
  have hI' := Kiter_integral hI (r + 1)
  rw [integral_P_eq hI] at hI'
  have h2 := mul_le_mul_of_nonneg_left h hs.le
  have h3 : (volume I.Δ.set).toReal * ((1 - I.lam) * I.Kiter (r + 1) 0) ≤
      (volume I.Δ.set).toReal * (-I.mean * (1 - I.lam ^ (r + 1))) := by
    nlinarith
  exact le_of_mul_le_mul_left h3 hV

/-- Bernoulli: `λ^N ‖P‖ < d(1 − λ)/16`. -/
theorem Nfix_bound (hI : I.Spec) : I.lam ^ I.Nfix * I.pnorm < I.d * (1 - I.lam) / 16 := by
  obtain ⟨hl1, hl2⟩ := lam_mem hI
  have hl0 : 0 < I.lam := by linarith
  have hs : 0 < 1 - I.lam := by linarith
  have hd := hI.d_pos
  have ha : 0 < I.lam⁻¹ - 1 := by
    rw [inv_eq_one_div, div_sub_one hl0.ne']; exact div_pos hs hl0
  have hN : (16 * I.pnorm / (I.d * (1 - I.lam))) / (I.lam⁻¹ - 1) < (I.Nfix : ℝ) := by
    unfold Nfix
    push_cast
    linarith [Nat.le_ceil ((16 * I.pnorm / (I.d * (1 - I.lam))) / (I.lam⁻¹ - 1))]
  rw [div_lt_iff₀ ha] at hN
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ I.lam⁻¹ - 1 by linarith) I.Nfix
  have he : (1 : ℝ) + (I.lam⁻¹ - 1) = I.lam⁻¹ := by ring
  rw [he, inv_pow] at hb
  have hpow : 0 < I.lam ^ I.Nfix := pow_pos hl0 _
  have hX : 16 * I.pnorm / (I.d * (1 - I.lam)) < (I.lam ^ I.Nfix)⁻¹ := by linarith
  have h1 : 16 * I.pnorm / (I.d * (1 - I.lam)) * I.lam ^ I.Nfix < 1 := by
    calc 16 * I.pnorm / (I.d * (1 - I.lam)) * I.lam ^ I.Nfix
        < (I.lam ^ I.Nfix)⁻¹ * I.lam ^ I.Nfix := mul_lt_mul_of_pos_right hX hpow
      _ = 1 := inv_mul_cancel₀ hpow.ne'
  have hds : 0 < I.d * (1 - I.lam) := mul_pos hd hs
  rw [div_mul_eq_mul_div, div_lt_one hds] at h1
  linarith

/-- The key identity `λ q = (2B + q)(1 − λ)`. -/
theorem lam_qq (hI : I.Spec) : I.lam * I.qq = (2 * I.bigB + I.qq) * (1 - I.lam) := by
  have hq := qq_pos hI
  have hB := I.one_le_bigB
  have hden : 2 * (I.bigB + I.qq) ≠ 0 := by positivity
  unfold lam
  field_simp
  ring

/-- **Finite comparator** (prop:cmp-fixed-point): `ℛ(K_N − P) ≤ K_N − 7d/8` on `Δ`. -/
theorem Kfin_gap (hI : I.Spec) :
    ∀ p ∈ I.Δ.set, rearrAll I.Δ (fun x => I.Kfin x - I.P x) p ≤ I.Kfin p - 7 * I.d / 8 := by
  have hΔ := hI.Δ_spec
  obtain ⟨hl1, hl2⟩ := lam_mem hI
  have hl0 : 0 ≤ I.lam := by linarith
  have hs : 0 < 1 - I.lam := by linarith
  have hd := hI.d_pos
  have hτ0 := hI.τ_pos
  have hτ1 := hI.τ_lt
  have hdβ := hI.d_lt_β
  have hdμ := hI.d_lt_mean
  have hB := I.one_le_bigB
  have hBd : I.d - I.pmin + 1 ≤ I.bigB := le_max_right _ _
  have hq := qq_pos hI
  have hlq := lam_qq hI
  have hμp := mean_le_pnorm hI
  have hη := Nfix_bound hI
  obtain ⟨c, hc⟩ : ∃ c, I.Nfix = c + 1 := ⟨_, rfl⟩
  have hKfin : I.Kfin = I.Kiter (c + 1) := by rw [Kfin, hc]
  rw [hc] at hη
  rw [hKfin]
  set N := c + 1 with hN
  set K := I.Kiter N with hKdef
  have hKc : ConvexCont I.Δ K := Kiter_convexCont hI N
  have h0 := zero_mem_set hΔ
  have hbdd := hΔ.compact.bddAbove_image hKc.1
  set M := sSup (K '' I.Δ.set) with hMdef
  have hKM : ∀ x ∈ I.Δ.set, K x ≤ M := fun x hx => le_csSup hbdd ⟨x, hx, rfl⟩
  have hstep := Kiter_step hI N
  have hpn := I.pnorm_nonneg
  have hlN : 0 ≤ I.lam ^ N := pow_nonneg hl0 _
  -- `λ^N μ ≤ λ^N ‖P‖ < d(1 − λ)/16`
  have hημ : I.lam ^ N * I.mean ≤ I.lam ^ N * I.pnorm := mul_le_mul_of_nonneg_left hμp hlN
  have hK0 := Kiter_origin hI c
  -- the gap of the max: `(1 − λ) M < −15d/16`
  have hgap : (1 - I.lam) * M < -(15 * I.d / 16) := by
    refine lt_of_not_ge fun hcon => ?_
    -- uniform bound `λK − P ≤ M − d/16` on `Δ`
    have hbd : ∀ x ∈ I.Δ.set, I.lam * K x - I.P x ≤ M - I.d / 16 := by
      intro x hx
      by_cases hout : x ∈ (I.Δ.dilate I.τ).set
      · -- core: `x = τ v` with `v ∈ Δ`
        set v : Moments m := I.τ⁻¹ • x with hv
        have hvmem : v ∈ I.Δ.set := by
          refine ⟨fun j => ?_, fun ν => ?_⟩
          · simp only [hv, Pi.smul_apply, smul_eq_mul]
            exact mul_nonneg (inv_nonneg.2 hτ0.le) (hx.1 j)
          · have h2 : ∑ j, I.Δ.b ν j * x j ≤ I.τ * I.Δ.ℓ ν := hout.2 ν
            have e : ∑ j, I.Δ.b ν j * v j = I.τ⁻¹ * ∑ j, I.Δ.b ν j * x j := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun j _ => by
                simp only [hv, Pi.smul_apply, smul_eq_mul]; ring
            rw [e, inv_mul_le_iff₀ hτ0]
            exact h2
        have hxv : x = I.τ • v + (1 - I.τ) • (0 : Moments m) := by
          funext j
          simp only [hv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_zero,
            add_zero]
          field_simp
        have hconv : K x ≤ I.τ * K v + (1 - I.τ) * K 0 := by
          have := hKc.2.2 hvmem h0 hτ0.le (show (0 : ℝ) ≤ 1 - I.τ by linarith)
            (show I.τ + (1 - I.τ) = 1 by ring)
          rw [← hxv] at this
          simpa only [smul_eq_mul] using this
        have hvM := hKM v hvmem
        have hPx := pmin_le hI x hx
        have hcore : K x ≤ I.τ * M + (1 - I.τ) * K 0 := by nlinarith
        -- multiply by `(1 − λ) λ ≥ 0`
        have hsl : 0 ≤ (1 - I.lam) * I.lam := mul_nonneg hs.le hl0
        have hA := mul_le_mul_of_nonneg_left hcore hsl
        have ht : 0 ≤ I.lam * (1 - I.τ) := mul_nonneg hl0 (by linarith)
        have hZ := mul_le_mul_of_nonneg_left hK0 ht
        have hM1 := mul_le_mul_of_nonneg_left hcon ht
        have hM2 := mul_le_mul_of_nonneg_left hcon hs.le
        have hlqq : I.lam * I.qq = I.lam * (1 - I.τ) * (I.mean - I.d) := by
          unfold qq; ring
        have hηt := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_le_of_lt hημ hη)) ht
        have hds : I.d * (1 - I.lam) / 16 ≤ I.d / 16 := by nlinarith
        have hηt2 := mul_le_mul_of_nonneg_left hds ht
        have key : (1 - I.lam) * (I.lam * K x) ≤
            (1 - I.lam) * (M + 15 * I.d / 16 - 2 * I.bigB - I.qq) := by
          nlinarith
        have := le_of_mul_le_mul_left key hs
        linarith
      · -- outer region
        have hPx := hI.outer x hx hout
        have := mul_le_mul_of_nonneg_left (hKM x hx) hl0
        linarith
    have hN1 := rearrAll_le_sup hΔ (Fstep_convexCont hI N) hbd
    have hsup : M ≤ M - I.d / 16 + I.lam ^ N * I.pnorm := by
      refine csSup_le ⟨K 0, 0, h0, rfl⟩ ?_
      rintro _ ⟨x, hx, rfl⟩
      have h1 := (abs_le.1 (hstep x hx)).1
      have h2 := hN1 x hx
      change rearrAll I.Δ (fun p => I.lam * I.Kiter N p - I.P p) x ≤ _ at h2
      change -(I.lam ^ N * I.pnorm) ≤
        rearrAll I.Δ (fun p => I.lam * I.Kiter N p - I.P p) x - K x at h1
      linarith
    nlinarith
  -- conclusion
  intro p hp
  have hsh := rearrAll_shift hΔ (F := fun x => K x - I.P x) (G := fun x => I.lam * K x - I.P x)
    ⟨hKc.1.sub hI.P_cont, hKc.2.sub hI.P_concave⟩ (Fstep_convexCont hI N)
    (c := (1 - I.lam) * M) (fun x hx => by
      have := mul_le_mul_of_nonneg_left (hKM x hx) hs.le
      show K x - I.P x ≤ I.lam * K x - I.P x + (1 - I.lam) * M
      linarith) p hp
  have h1 := (abs_le.1 (hstep p hp)).2
  change rearrAll I.Δ (fun p => I.lam * I.Kiter N p - I.P p) p - K p ≤ _ at h1
  have : I.lam ^ N * I.pnorm < I.d / 16 := by nlinarith
  linarith

end CmpInput

end SymplecticPacking.HighDim
