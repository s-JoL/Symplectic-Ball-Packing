import SymplecticPacking.Effective.PackingCertificateField
import SymplecticPacking.Effective.PackingCertificateTarget

/-!
# Uniform source neighbourhoods

Uniform source neighbourhoods for the finite polynomial certificate.
-/

noncomputable section
namespace SymplecticPacking.Effective.PackingCertificate
open Set Metric
open scoped Topology NNReal

/-- Two genuine solutions of the same field retain a uniform initial-value bound. -/
theorem initial_stability {d : ℕ} {F : ℝ → (Fin d → ℝ) → (Fin d → ℝ)}
    {L : ℝ≥0} (hF : ∀ t, LipschitzWith L (F t))
    {y z : ℝ → Fin d → ℝ} (hy : IsIntegralCurveOn y F (Icc 0 1))
    (hz : IsIntegralCurveOn z F (Icc 0 1)) (t : ℝ) (ht : t ∈ Icc 0 1) :
    dist (z t) (y t) ≤ dist (z 0) (y 0) * Real.exp L := by
  have hh := flow_error_with_initial hF (G := F) (η := 0)
    (fun _ _ => by simp) hy hz (ρ := dist (z 0) (y 0)) le_rfl t ht
  rw [gronwallBound_ε0] at hh
  refine hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) dist_nonneg)
  nlinarith [L.coe_nonneg, ht.2]

/-- A known smaller target radius makes compactness unnecessary: one radius gap
pays for the entire neighbourhood. -/
theorem source_neighbourhood_of_radius {d : ℕ}
    {F : ℝ → (Fin d → ℝ) → (Fin d → ℝ)} {L : ℝ≥0}
    (hF : ∀ t, LipschitzWith L (F t))
    {K : Set (Fin d → ℝ)} {B R₀ R : ℝ} (hgap : R₀ < R)
    (hsource : ∀ x ∈ K, ∃ y : ℝ → Fin d → ℝ, y 0=x ∧
      IsIntegralCurveOn y F (Icc 0 1) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ j, |y t j|+1 < B/2) ∧
      ‖l2Vector (y 1)‖ ≤ R₀) :
    ∃ ν μ : ℝ, 0 < ν ∧ 0 < μ ∧
      ∀ z : ℝ → Fin d → ℝ, IsIntegralCurveOn z F (Icc 0 1) →
        (∃ x ∈ K, dist (z 0) x < ν) →
        (∀ t ∈ Icc (0:ℝ) 1, ∀ j, |z t j|+1/2 < B/2) ∧
        ‖l2Vector (z 1)‖+μ < R := by
  let μ : ℝ := (R-R₀)/2
  have hμ : 0 < μ := by dsimp [μ]; linarith
  let ε : ℝ := min (1/4) (μ/((d:ℝ)+1))
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hμ (by positivity))
  have hεq : ε ≤ 1/4 := min_le_left _ _
  have hεμ : (d:ℝ)*ε < μ := by
    have hh := (le_div_iff₀ (by positivity : 0 < (d:ℝ)+1)).mp
      (min_le_right (1/4:ℝ) (μ/((d:ℝ)+1)))
    change ε*((d:ℝ)+1) ≤ μ at hh
    nlinarith
  let ν : ℝ := ε/(Real.exp L+1)
  have hν : 0 < ν := div_pos hε (by positivity)
  have hνexp : ν*Real.exp L < ε := by
    have hh : ν*(Real.exp L+1)=ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  refine ⟨ν,μ,hν,hμ,?_⟩
  intro z hz ⟨x,hx,hnear⟩
  obtain ⟨y,hy0,hy,hplateau,htarget⟩ := hsource x hx
  have hclose : ∀ t ∈ Icc (0:ℝ) 1, ‖z t-y t‖ < ε := by
    intro t ht
    have hh := initial_stability hF hy hz t ht
    rw [hy0] at hh
    have hh' := mul_lt_mul_of_pos_right hnear (Real.exp_pos (L:ℝ))
    have hd : ‖z t-y t‖ ≤ dist (z 0) x*Real.exp L := by
      simpa only [dist_eq_norm] using hh
    exact hd.trans_lt (hh'.trans hνexp)
  constructor
  · intro t ht j
    have hc := (norm_le_pi_norm (z t-y t) j).trans_lt (hclose t ht)
    have hp := hplateau t ht j
    have htri := abs_add_le (z t j-y t j) (y t j)
    simp only [Pi.sub_apply,Real.norm_eq_abs] at hc
    rw [sub_add_cancel] at htri
    linarith
  · have hc := l2_norm_le_dim_mul hε.le (hclose 1 (by norm_num)).le
    rw [l2Vector_sub] at hc
    have htri : ‖l2Vector (z 1)‖ ≤ ‖l2Vector (z 1)-l2Vector (y 1)‖+‖l2Vector (y 1)‖ :=
      by simpa only [add_comm] using norm_le_insert' (l2Vector (z 1)) (l2Vector (y 1))
    dsimp [μ] at hεμ ⊢
    linarith

end SymplecticPacking.Effective.PackingCertificate
