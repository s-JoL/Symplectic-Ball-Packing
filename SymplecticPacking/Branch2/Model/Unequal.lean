import SymplecticPacking.Branch2.Params
import SymplecticPacking.Branch2.Comparator.Main
import SymplecticPacking.Branch2.Planar.Interface
import SymplecticPacking.Branch2.Model.Data

/-!
# The cubic-model data for unequal capacities (`thm:cub-packing`, general case)

From normalised capacities `ρ : Fin k → ℝ` (`0 < ρ_i < 1/3`, `Σρ_i² < 1`):

* the auxiliary data of `lem:cub-auxiliary` (`Branch2/Params.lean`): `a_i`, `h`, `τ`, `μ`, `γ`,
  `d = min(μ, γ)/2`, `d_n`;
* the comparator input `cmpInput ρ` (`P = P_b`, `P_min = -Σa_i`, `P̄ = 3 + Σa_i`, `L_P = 9 + k`)
  and the smooth comparison function `Kc ρ = (cmpInput ρ).Kcmp` with
  `R(K - P_b) ≤ K - 13d/16` (`Cmp.Input.Hyp.Kcmp_gap`);
* the planar input `planarInput ρ` (`F = K - P_b`, `U₀ = K - H_b + Σ softcap_i`, `e = d/16`,
  `σ₀ = d/256`) and the five-segment path `(planarInput ρ).planarPath`;
* `g = 3d/4`.

`cubicDataOf_valid`: the resulting `CubicData` is valid; the comparison field follows from
`K(I) - F(p(q̂₁z)) ≥ K(I) - R F(I) - d/16 ≥ 13d/16 - d/16 = g ≥ 31g/32`.
-/

noncomputable section

namespace SymplecticPacking.Branch2

open Set
open scoped Real ContDiff

variable {k : ℕ} (ρ : Fin k → ℝ)

/-- A `Fin k`-indexed family read with ball indices `1 … k` (`0` elsewhere). -/
def natIdx (v : Fin k → ℝ) (i : ℕ) : ℝ := if h : 1 ≤ i ∧ i ≤ k then v ⟨i - 1, by omega⟩ else 0

lemma natIdx_succ (v : Fin k → ℝ) (i : Fin k) : natIdx v (i.val + 1) = v i := by
  unfold natIdx
  rw [dif_pos ⟨by omega, i.isLt⟩]
  congr 1

lemma sum_Icc_natIdx (v : Fin k → ℝ) (f : ℝ → ℝ) :
    ∑ i ∈ Finset.Icc 1 k, f (natIdx v i) = ∑ i : Fin k, f (v i) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  rw [← Fin.sum_univ_eq_sum_range (fun j => f (natIdx v (1 + j)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [add_comm, natIdx_succ]

/-- The comparator input. -/
def cmpInput : Cmp.Input where
  h := height ρ
  P := Pb ρ
  tau := tau ρ
  mu := meanP ρ
  beta := gammaOut ρ
  d := dGap ρ
  Pmin := -∑ i, aux ρ i
  Pbar := 3 + ∑ i, aux ρ i
  LP := 9 + k

/-- The smooth comparison function. -/
def Kc : ℝ → ℝ := (cmpInput ρ).Kcmp

/-- Smoothed cap `[(a - p) + √((a - p)² + ε²)]/2`. -/
def softcap (ε a p : ℝ) : ℝ := ((a - p) + Real.sqrt ((a - p) ^ 2 + ε ^ 2)) / 2

/-- The planar input. -/
def planarInput : Planar.PlanarInput where
  h := height ρ
  e := dGap ρ / 16
  L := (cmpInput ρ).lipK + 9 + k
  F := fun p => Kc ρ p - Pb ρ p
  U0 := fun p => Kc ρ p - Hb p + ∑ i, softcap (dGap ρ / (128 * k)) (aux ρ i) p
  sig := dGap ρ / 256

/-- **The cubic-model data of the unequal construction.** -/
def cubicDataOf : CubicData where
  k := k
  rho := natIdx ρ
  a := natIdx (aux ρ)
  h := height ρ
  dn := dn ρ
  g := 3 * dGap ρ / 4
  K := Kc ρ
  path := (planarInput ρ).planarPath

variable {ρ}

/-- The comparator hypotheses hold for `P_b`. -/
theorem Hyp.cmpInput_hyp (H : Hyp ρ) : (cmpInput ρ).Hyp := by
  have hsum : 0 ≤ ∑ i, aux ρ i := Finset.sum_nonneg fun i _ => (H.aux_pos i).le
  have hcap_le : ∀ p, 0 ≤ p → ∀ i, max (aux ρ i - p) 0 ≤ aux ρ i := fun p hp i =>
    max_le (by linarith) (H.aux_pos i).le
  have hcap_sum : ∀ p, 0 ≤ p → ∑ i, max (aux ρ i - p) 0 ≤ ∑ i, aux ρ i := fun p hp =>
    Finset.sum_le_sum fun i _ => hcap_le p hp i
  have hcap_nonneg : ∀ p, 0 ≤ ∑ i, max (aux ρ i - p) 0 := fun p =>
    Finset.sum_nonneg fun i _ => le_max_right _ _
  have hPmin : ∀ p ∈ Icc 0 (height ρ), -∑ i, aux ρ i ≤ Pb ρ p := by
    intro p hp
    have := hcap_sum p hp.1
    have : 0 ≤ Hb p := by unfold Hb; linarith [hp.2, H.height_lt_third]
    unfold Pb; linarith
  refine ⟨H.height_pos, H.Pb_continuous, H.Pb_concave.subset (subset_univ _) (convex_Icc _ _),
    ?_, H.tau_pos, H.tau_lt_one, fun p hp => (H.Pb_outer hp.1 hp.2).2, H.dGap_pos,
    H.dGap_lt_meanP, H.dGap_lt_gammaOut, hPmin, ?_, by show (0 : ℝ) < 3 + _; linarith,
    by show (0 : ℝ) ≤ 9 + k; positivity, ?_⟩
  · show ∫ p in (0 : ℝ)..height ρ, Pb ρ p = meanP ρ * height ρ
    rw [H.integral_Pb]
    unfold meanP
    have := H.height_pos.ne'
    field_simp
  · intro p hp
    show |Pb ρ p| ≤ 3 + ∑ i, aux ρ i
    have h1 := hPmin p hp
    have h2 : Pb ρ p ≤ 3 := by
      have := hcap_nonneg p
      unfold Pb Hb; linarith [hp.1]
    rw [abs_le]; constructor <;> linarith
  · intro x hx y hy
    show |Pb ρ x - Pb ρ y| ≤ (9 + k) * |x - y|
    have e : Pb ρ x - Pb ρ y = -9 * (x - y) - ∑ i, (max (aux ρ i - x) 0 - max (aux ρ i - y) 0) := by
      unfold Pb Hb; rw [Finset.sum_sub_distrib]; ring
    rw [e]
    have hs : |∑ i, (max (aux ρ i - x) 0 - max (aux ρ i - y) 0)| ≤ k * |x - y| := by
      calc |∑ i, (max (aux ρ i - x) 0 - max (aux ρ i - y) 0)|
          ≤ ∑ i, |max (aux ρ i - x) 0 - max (aux ρ i - y) 0| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i : Fin k, |x - y| := Finset.sum_le_sum fun i _ => by
            refine (abs_max_sub_max_le_abs _ _ _).trans ?_
            rw [show aux ρ i - x - (aux ρ i - y) = -(x - y) by ring, abs_neg]
        _ = k * |x - y| := by simp
    calc |-9 * (x - y) - ∑ i, (max (aux ρ i - x) 0 - max (aux ρ i - y) 0)|
        ≤ |-9 * (x - y)| + |∑ i, (max (aux ρ i - x) 0 - max (aux ρ i - y) 0)| := abs_sub _ _
      _ ≤ 9 * |x - y| + k * |x - y| := by
          have : |(-9 : ℝ) * (x - y)| = 9 * |x - y| := by rw [abs_mul]; norm_num
          rw [this]; exact add_le_add le_rfl hs
      _ = (9 + k) * |x - y| := by ring

lemma sqrt_sq_add_comb {ε u v t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (hts : t + s = 1) :
    Real.sqrt ((t * u + s * v) ^ 2 + ε ^ 2) ≤
      t * Real.sqrt (u ^ 2 + ε ^ 2) + s * Real.sqrt (v ^ 2 + ε ^ 2) := by
  set A := Real.sqrt (u ^ 2 + ε ^ 2) with hAdef
  set B := Real.sqrt (v ^ 2 + ε ^ 2) with hBdef
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hA : A ^ 2 = u ^ 2 + ε ^ 2 := Real.sq_sqrt (by positivity)
  have hB : B ^ 2 = v ^ 2 + ε ^ 2 := Real.sq_sqrt (by positivity)
  have hAB : u * v + ε ^ 2 ≤ A * B := by
    by_contra hc
    push Not at hc
    have h0 : 0 ≤ A * B := mul_nonneg hA0 hB0
    have h1 := mul_self_lt_mul_self h0 hc
    have h2 : (A * B) * (A * B) = (u ^ 2 + ε ^ 2) * (v ^ 2 + ε ^ 2) := by
      rw [← hA, ← hB]; ring
    nlinarith [sq_nonneg (ε * (u - v))]
  have hR : 0 ≤ t * A + s * B := by positivity
  rw [← Real.sqrt_sq hR]
  apply Real.sqrt_le_sqrt
  have hs' : s = 1 - t := by linarith
  subst hs'
  have hm := mul_le_mul_of_nonneg_left hAB (mul_nonneg ht hs)
  have key : (t * A + (1 - t) * B) ^ 2 =
      t ^ 2 * (u ^ 2 + ε ^ 2) + (1 - t) ^ 2 * (v ^ 2 + ε ^ 2) + 2 * (t * (1 - t) * (A * B)) := by
    rw [← hA, ← hB]; ring
  have iden : (t * u + (1 - t) * v) ^ 2 + ε ^ 2 =
      t ^ 2 * (u ^ 2 + ε ^ 2) + (1 - t) ^ 2 * (v ^ 2 + ε ^ 2) + 2 * (t * (1 - t) * (u * v + ε ^ 2)) := by
    ring
  rw [key, iden]; linarith

lemma softcap_convex {ε a : ℝ} : ConvexOn ℝ univ (fun p => softcap ε a p) := by
  refine ⟨convex_univ, fun x _ y _ t s ht hs hts => ?_⟩
  simp only [smul_eq_mul, softcap]
  have e : a - (t * x + s * y) = t * (a - x) + s * (a - y) := by
    linear_combination (-a) * hts
  rw [e]
  have := sqrt_sq_add_comb (ε := ε) (u := a - x) (v := a - y) ht hs hts
  nlinarith [this]

lemma softcap_contDiff {ε a : ℝ} (hε : ε ≠ 0) : ContDiff ℝ ∞ (fun p => softcap ε a p) := by
  unfold softcap
  refine ContDiff.div_const (ContDiff.add (contDiff_const.sub contDiff_id) ?_) _
  refine ContDiff.sqrt (((contDiff_const.sub contDiff_id).pow 2).add contDiff_const) ?_
  intro p
  have : 0 < ε ^ 2 := by positivity
  positivity

lemma softcap_bounds {ε : ℝ} (hε : 0 ≤ ε) (a p : ℝ) :
    max (a - p) 0 ≤ softcap ε a p ∧ softcap ε a p ≤ max (a - p) 0 + ε / 2 := by
  unfold softcap
  set x := a - p
  have h1 : |x| ≤ Real.sqrt (x ^ 2 + ε ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg ε])
  have h2 : Real.sqrt (x ^ 2 + ε ^ 2) ≤ |x| + ε := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ |x| + ε)]
    apply Real.sqrt_le_sqrt
    have : |x| ^ 2 = x ^ 2 := sq_abs x
    nlinarith [abs_nonneg x]
  have hm : max x 0 = (x + |x|) / 2 := by
    rcases le_total x 0 with hx | hx
    · rw [max_eq_right hx, abs_of_nonpos hx]; ring
    · rw [max_eq_left hx, abs_of_nonneg hx]; ring
  rw [hm]; constructor <;> linarith

lemma convexOn_univ_finsum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i, ConvexOn ℝ univ (f i)) : ConvexOn ℝ univ (fun p => ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using convexOn_const (0 : ℝ) (convex_univ (𝕜 := ℝ) (E := ℝ))
  | insert a s ha ih =>
    have := (hf a).add ih
    convert this using 1
    funext p
    simp [Finset.sum_insert ha]

lemma Hb_concave : ConcaveOn ℝ univ Hb := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, Hb]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith

/-- The planar hypotheses hold for `F = K - P_b`. -/
theorem Hyp.planarInput_hyp (H : Hyp ρ) : (planarInput ρ).Hyp := by
  have hC := H.cmpInput_hyp
  have hd := H.dGap_pos
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast H.one_le
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  set ε := dGap ρ / (128 * k) with hεdef
  have hε : 0 < ε := by positivity
  have hKconv : ConvexOn ℝ univ (Kc ρ) := hC.Kcmp_convex
  have hKlip : ∀ x y, |Kc ρ x - Kc ρ y| ≤ (cmpInput ρ).lipK * |x - y| := fun x y =>
    Cmp.smoothK_lipschitz hC.h_pos.le hC.lipK_nonneg hC.wSmooth_pos (hC.iter_continuousOn _) x y
  have hsum_lo : ∀ p, ∑ i, max (aux ρ i - p) 0 ≤ ∑ i, softcap ε (aux ρ i) p := fun p =>
    Finset.sum_le_sum fun i _ => (softcap_bounds hε.le _ _).1
  have hsum_hi : ∀ p, ∑ i, softcap ε (aux ρ i) p ≤ ∑ i, max (aux ρ i - p) 0 + dGap ρ / 256 := by
    intro p
    calc ∑ i, softcap ε (aux ρ i) p ≤ ∑ i : Fin k, (max (aux ρ i - p) 0 + ε / 2) :=
          Finset.sum_le_sum fun i _ => (softcap_bounds hε.le _ _).2
      _ = ∑ i, max (aux ρ i - p) 0 + k * (ε / 2) := by
          rw [Finset.sum_add_distrib]; simp
      _ = ∑ i, max (aux ρ i - p) 0 + dGap ρ / 256 := by
          rw [hεdef]; field_simp; ring
  refine ⟨H.height_pos, by show (0 : ℝ) < dGap ρ / 16; positivity,
    by show (0 : ℝ) ≤ (cmpInput ρ).lipK + 9 + k; linarith [hC.lipK_nonneg], ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, by show (0 : ℝ) ≤ dGap ρ / 256; positivity,
    by show dGap ρ / 256 ≤ dGap ρ / 16 / 16; linarith⟩
  · exact (hC.Kcmp_contDiff.continuous.sub H.Pb_continuous).continuousOn
  · exact (hKconv.subset (subset_univ _) (convex_Icc _ _)).sub
      (H.Pb_concave.subset (subset_univ _) (convex_Icc _ _))
  · intro x hx y hy
    show |(Kc ρ x - Pb ρ x) - (Kc ρ y - Pb ρ y)| ≤ ((cmpInput ρ).lipK + 9 + k) * |x - y|
    have h1 := hKlip x y
    have h2 : |Pb ρ x - Pb ρ y| ≤ (9 + k) * |x - y| := hC.lip x hx y hy
    calc |(Kc ρ x - Pb ρ x) - (Kc ρ y - Pb ρ y)|
        = |(Kc ρ x - Kc ρ y) - (Pb ρ x - Pb ρ y)| := by ring_nf
      _ ≤ |Kc ρ x - Kc ρ y| + |Pb ρ x - Pb ρ y| := abs_sub _ _
      _ ≤ (cmpInput ρ).lipK * |x - y| + (9 + k) * |x - y| := add_le_add h1 h2
      _ = ((cmpInput ρ).lipK + 9 + k) * |x - y| := by ring
  · exact (hC.Kcmp_contDiff.sub (by unfold Hb; fun_prop)).add
      (ContDiff.sum fun i _ => softcap_contDiff hε.ne')
  · exact (hKconv.sub Hb_concave).add
      (convexOn_univ_finsum Finset.univ (fun i p => softcap ε (aux ρ i) p)
        fun i => softcap_convex)
  · intro p _
    show Kc ρ p - Pb ρ p ≤ Kc ρ p - Hb p + ∑ i, softcap ε (aux ρ i) p
    have := hsum_lo p
    unfold Pb; linarith
  · intro p _
    show Kc ρ p - Hb p + ∑ i, softcap ε (aux ρ i) p ≤ Kc ρ p - Pb ρ p + dGap ρ / 256
    have := hsum_hi p
    unfold Pb; linarith

lemma cubicDataOf_F (p : ℝ) : (cubicDataOf ρ).F p = Kc ρ p - Pb ρ p := by
  simp only [CubicData.F, CubicData.Pb, CubicData.Hb, cubicDataOf, Pb, Hb]
  rw [sum_Icc_natIdx (aux ρ) (fun x => max (x - p) 0)]

/-- **The unequal data are valid.** -/
theorem Hyp.cubicDataOf_valid (H : Hyp ρ) : (cubicDataOf ρ).Valid := by
  have hC := H.cmpInput_hyp
  have hPl := H.planarInput_hyp
  have hk := H.one_le
  have hd := H.dGap_pos
  refine ⟨H.one_le, ?_, ?_, ?_, H.height_pos, H.height_lt_dn, H.dn_lt_third, ?_, ?_, ?_,
    hPl.planarPath_ordinary, Planar.PlanarInput.planarPath_h (D := planarInput ρ), ?_⟩
  · intro i h1 h2
    show 0 < natIdx ρ i
    unfold natIdx; rw [dif_pos ⟨h1, h2⟩]; exact H.pos _
  · intro i h1 h2
    show natIdx ρ i < natIdx (aux ρ) i
    unfold natIdx; rw [dif_pos ⟨h1, h2⟩, dif_pos ⟨h1, h2⟩]; exact H.rho_lt_aux _
  · intro i h1 h2
    show natIdx (aux ρ) i < height ρ
    unfold natIdx; rw [dif_pos ⟨h1, h2⟩]; exact H.aux_lt_height _
  · show 0 < 3 * dGap ρ / 4; linarith
  · show 3 * dGap ρ / 4 ≤ 3 * (1 - 3 * height ρ)
    have := H.dGap_lt_gammaOut; unfold gammaOut at this; linarith
  · exact hC.Kcmp_contDiff
  · intro z hz
    rw [cubicDataOf_F]
    have hI : π * ‖z‖ ^ 2 ∈ Icc 0 (height ρ) := ⟨by positivity, hz⟩
    have h1 := hPl.planarPath_comparison hz
    have h2 := hC.Kcmp_gap hI
    show 31 * (3 * dGap ρ / 4) / 32 ≤
      Kc ρ (π * ‖z‖ ^ 2) - (Kc ρ (π * ‖Qhat.qhat (planarInput ρ).planarPath 1 z‖ ^ 2) -
        Pb ρ (π * ‖Qhat.qhat (planarInput ρ).planarPath 1 z‖ ^ 2))
    have e1 : (planarInput ρ).F = fun p => Kc ρ p - Pb ρ p := rfl
    have e2 : (planarInput ρ).h = height ρ := rfl
    have e3 : (planarInput ρ).e = dGap ρ / 16 := rfl
    rw [e1, e2, e3] at h1
    have e4 : (cmpInput ρ).h = height ρ := rfl
    have e5 : (cmpInput ρ).P = Pb ρ := rfl
    have e6 : (cmpInput ρ).d = dGap ρ := rfl
    rw [e4, e5, e6] at h2
    have e7 : (cmpInput ρ).Kcmp = Kc ρ := rfl
    rw [e7] at h2
    linarith

end SymplecticPacking.Branch2
