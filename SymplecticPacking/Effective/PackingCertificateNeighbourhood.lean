import SymplecticPacking.Effective.PackingCertificateNeighbourhoodCore
import SymplecticPacking.Effective.PackingCertificateOutput
import SymplecticPacking.General.CompileFlowTube

/-!
# Source neighbourhoods of compiled candidates

Compiled candidates have uniform source neighbourhoods.
-/

noncomputable section
namespace SymplecticPacking.Effective.PackingCertificate
open Set Metric
open scoped Topology NNReal

/-- A safe Hamiltonian trajectory supplies the clipped-field reference
trajectory. The change from Euclidean to sup norm is an explicit linear map. -/
theorem output_reference_curve {n k B : ℕ} (e : PackingPolynomial.Expr) (hB : 0 < B)
    {C : ℝ} {c : Fin k → ℝ} {s : Fin k → Problem.E n}
    (hpack : Problem.PackingSpec n k C c s (PackingPolynomial.output n B e).hamiltonian)
    (hplateau : ∀ i, ∀ x ∈ Problem.capBall (s i) (c i),
      ∀ γ : ℝ → Problem.E n, γ 0=x →
      IsIntegralCurveOn γ (Problem.hamVF (PackingPolynomial.output n B e).hamiltonian) (Icc 0 1) →
      ∀ t ∈ Icc (0:ℝ) 1, ‖γ t‖+1 < (B:ℝ)/2)
    (i : Fin k) (x : Fin (2*n) → ℝ) (hx : l2Vector x ∈ Problem.capBall (s i) (c i)) :
    ∃ y : ℝ → Fin (2*n) → ℝ, y 0=x ∧
      IsIntegralCurveOn y (PackingPolynomial.field n B e) (Icc 0 1) ∧
      (∀ t ∈ Icc (0:ℝ) 1, ∀ j, |y t j|+1 < (B:ℝ)/2) ∧
      ‖l2Vector (y 1)‖ ≤ Real.sqrt (C/Real.pi) := by
  obtain ⟨γ,hγ0,hγ⟩ := hpack.exists_curve i (l2Vector x) hx
  let L : Problem.E n →L[ℝ] (Fin (2*n) → ℝ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (2*n) => ℝ)).toContinuousLinearMap
  let y : ℝ → Fin (2*n) → ℝ := fun t => L (γ t)
  have hy0 : y 0=x := by
    change (fun j => γ 0 j)=x
    rw [hγ0]
    rfl
  have hp := hplateau i (l2Vector x) hx γ hγ0 (hγ.isIntegralCurveOn (Icc 0 1))
  have hycoord : ∀ t j, y t j = γ t j := fun _ _ => rfl
  have hyl2 : ∀ t, l2Vector (y t)=γ t := fun _ => rfl
  have hy : IsIntegralCurveOn y (PackingPolynomial.field n B e) (Icc 0 1) := by
    intro t ht
    have hc := L.hasFDerivAt.comp_hasDerivWithinAt t (hγ.isIntegralCurveOn (Icc 0 1) t ht)
    change HasDerivWithinAt y
      (L (Problem.hamVF (PackingPolynomial.output n B e).hamiltonian t (γ t))) (Icc 0 1) t at hc
    have hfield := PackingPolynomial.field_eq_output_of_plateau n B e hB ht
      (z := γ t) (fun j => by
        have hj := PiLp.norm_apply_le (γ t) j
        rw [Real.norm_eq_abs] at hj
        linarith [hp t ht])
    have heq : PackingPolynomial.field n B e t (y t) =
      L (Problem.hamVF (PackingPolynomial.output n B e).hamiltonian t (γ t)) := by
      exact congrArg L hfield
    rw [heq]
    exact hc
  refine ⟨y,hy0,hy,?_,?_⟩
  · intro t ht j
    rw [hycoord]
    have hj := PiLp.norm_apply_le (γ t) j
    rw [Real.norm_eq_abs] at hj
    linarith [hp t ht]
  · rw [hyl2]
    have hh := hpack.maps_into i (l2Vector x) hx γ hγ0 (hγ.isIntegralCurveOn (Icc 0 1))
    change Real.pi*‖γ 1-0‖^2 < C at hh
    rw [sub_zero] at hh
    apply Real.le_sqrt_of_sq_le
    exact (le_div_iff₀ Real.pi_pos).mpr (by nlinarith)

/-- The finite compiler supplies a candidate and a genuine source
neighbourhood with fixed plateau and terminal margins. Only a smaller smooth
packing is assumed; the polynomial, its safe tube and the neighbourhood are proved. -/
theorem exists_compiled_source_neighbourhood {n k : ℕ} {C₀ Cmid C : ℝ}
    {c : Fin k → ℝ} {s : Fin k → Problem.E n} {H : ℝ → Problem.E n → ℝ}
    (hpack : Problem.PackingSpec n k C₀ c s H) (hC₀ : 0 < C₀)
    (hCmid : C₀ < Cmid) (hC : Cmid < C) :
    ∃ B : ℕ, ∃ e : PackingPolynomial.Expr, 1 ≤ B ∧
      Problem.PackingSpec n k Cmid c s (PackingPolynomial.output n B e).hamiltonian ∧
      ∃ ν μ : ℝ, 0 < ν ∧ 0 < μ ∧
        ∀ z : ℝ → Fin (2*n) → ℝ,
          IsIntegralCurveOn z (PackingPolynomial.field n B e) (Icc 0 1) →
          (∃ x : Fin (2*n) → ℝ,
            (∃ i, l2Vector x ∈ Problem.capBall (s i) (c i)) ∧ dist (z 0) x < ν) →
          (∀ t ∈ Icc (0:ℝ) 1, ∀ j, |z t j|+1/2 < (B:ℝ)/2) ∧
          ‖l2Vector (z 1)‖+μ < Real.sqrt (C/Real.pi) := by
  obtain ⟨D,hD,hplateau⟩ := General.Compile.exists_compilationDatum_plateau hpack hC₀ hCmid
  obtain ⟨e,he⟩ := PackingPolynomial.toPolynomial_surjective (2*n+1) D.P
  have hout : (PackingPolynomial.output n D.B e).hamiltonian=D.Hfin := by
    change General.Compile.finiteHam n D.B (PackingPolynomial.toPolynomial (2*n+1) e)=D.Hfin
    rw [he]
    rfl
  have hB : 1 ≤ D.B := by have hh := D.B_gt_dim; omega
  have hBp : 0 < D.B := by omega
  have hdpack : Problem.PackingSpec n k Cmid c s
      (PackingPolynomial.output n D.B e).hamiltonian := by simpa only [hout] using hD
  refine ⟨D.B,e,hB,hdpack,?_⟩
  have hmidpos : 0 < Cmid := hC₀.trans hCmid
  have hrad : Real.sqrt (Cmid/Real.pi) < Real.sqrt (C/Real.pi) :=
    Real.sqrt_lt_sqrt (by positivity : 0 ≤ Cmid/Real.pi)
      ((div_lt_div_iff_of_pos_right Real.pi_pos).mpr hC)
  apply source_neighbourhood_of_radius (PackingPolynomial.field_lipschitz n D.B e hB) hrad
    (K := {x | ∃ i, l2Vector x ∈ Problem.capBall (s i) (c i)})
  intro x ⟨i,hx⟩
  apply output_reference_curve e hBp hdpack ?_ i x hx
  simpa only [hout] using hplateau

end SymplecticPacking.Effective.PackingCertificate
