import SymplecticPacking.General.Ham.Flow
import SymplecticPacking.General.Ham.Symp
import SymplecticPacking.Return.Flow

/-!
# The global flow of a compact Hamiltonian

The global flow of a compact Hamiltonian preserves the standard form.
-/

noncomputable section
namespace SymplecticPacking.General.Ham
open Set Function Filter Metric Module
open OAI.PackingSufficiencySupport.Hamiltonian
open SymplecticPacking.Problem
open scoped ContDiff Topology
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance globalFlowRealNormedSpace : NormedSpace ℝ ℝ := NormedField.toNormedSpace
local instance globalFlowContinuousSMul : ContinuousSMul ℝ (E n) := IsBoundedSMul.continuousSMul

private theorem derivative_slice {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ℝ × V → ℝ} (hf : Differentiable ℝ f) (p : ℝ × V) (w : V) :
    fderiv ℝ (fun x => f (p.1,x)) p.2 w=fderiv ℝ f p (0,w) := by
  have hi : HasFDerivAt (fun x : V => (p.1,x)) (ContinuousLinearMap.inr ℝ ℝ V) p.2 :=
    hasFDerivAt_prodMk_right p.1 p.2
  have hd := (hf p).hasFDerivAt.comp p.2 hi
  have he := congrArg (fun L : V →L[ℝ] ℝ => L w) hd.fderiv
  simpa +instances only [Function.comp_def,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inr_apply] using he

theorem omega0L_isInvertible : (omega0L (n:=n)).IsInvertible := by
  have hi : Injective (omega0L (n:=n)) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    apply omega0_nondegenerate
    intro w
    have hh := congrArg (fun L : E n →L[ℝ] ℝ => L w) hv
    simpa only [omega0L_apply,ContinuousLinearMap.zero_apply] using hh
  have hs : Surjective (omega0L (n:=n)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by
        rw [← (LinearMap.toContinuousLinearMap : ((E n) →ₗ[ℝ] ℝ) ≃ₗ[ℝ]
          ((E n) →L[ℝ] ℝ)).finrank_eq]
        exact Subspace.dual_finrank_eq.symm)).mp hi
  exact ⟨(LinearEquiv.ofBijective (omega0L (n:=n)).toLinearMap ⟨hi,hs⟩).toContinuousLinearEquiv,rfl⟩

/-- The sign conversion to the library's convention `ι_X ω = -dH`. -/
theorem problemField_eq_negative_hamiltonianField {H : ℝ → E n → ℝ}
    (hH : ContDiff ℝ ∞ (Function.uncurry H)) (p : ℝ × E n) :
    Problem.hamVF H p.1 p.2=hamiltonianField omega0L (fun q => -H q.1 q.2) p := by
  have hs : DifferentiableAt ℝ (H p.1) p.2 :=
    (hH.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) p.2
  apply hamVF_eq_of_hasFDerivAt hs.hasFDerivAt
  intro w
  have he := derivative_slice (hH.differentiable (by simp)) p w
  have hc := hamiltonianField_contraction omega0L_isInvertible (fun q => -H q.1 q.2) p w
  simp only [fderiv_fun_neg,omega0L_apply,ContinuousLinearMap.neg_apply,neg_neg] at hc
  calc
    _ = (fderiv ℝ (Function.uncurry H) p) (0,w) := by
      simpa +instances only [Function.uncurry,PiLp.normedAddCommGroup,
        PiLp.seminormedAddCommGroup,PiLp.normedSpace] using he
    _ = _ := hc.symm

theorem compact_hamiltonian_csField {H : ℝ → E n → ℝ}
    (hH : ContDiff ℝ ∞ (Function.uncurry H)) (hK : HasCompactSupport (Function.uncurry H)) :
    Return.CSField (Problem.hamVF H) := by
  refine ⟨hamField_contDiff hH,?_⟩
  have he : (fun p : ℝ × E n => Problem.hamVF H p.1 p.2)=
      hamiltonianField omega0L (fun q => -H q.1 q.2) := funext (problemField_eq_negative_hamiltonianField hH)
  rw [he]
  exact hK.neg.of_isClosed_subset (isClosed_tsupport _)
    (hamiltonianField_support omega0L (fun q => -H q.1 q.2))

theorem hasCompactSupport_of_space_time {H : ℝ → E n → ℝ}
    {K : Set (E n)} (hK : IsCompact K) (hspace : ∀ t,∀ x∉K,H t x=0)
    (htime : ∀ t x,t≤0 ∨ 1≤t → H t x=0) : HasCompactSupport (Function.uncurry H) := by
  have hKt : IsCompact (Icc (0:ℝ) 1) := isCompact_Icc
  apply HasCompactSupport.intro (hKt.prod hK)
  rintro ⟨t,x⟩ hx
  rcases not_and_or.mp hx with ht | hx
  · apply htime t x
    rcases not_and_or.mp ht with ht | ht
    · exact Or.inl (le_of_lt (lt_of_not_ge ht))
    · exact Or.inr (le_of_lt (lt_of_not_ge ht))
  · exact hspace t x hx

/-- Each flow slice is a smooth symplectic diffeomorphism, not merely a
chosen endpoint with the same packing conclusion. -/
theorem compact_hamiltonian_flow {H : ℝ → E n → ℝ}
    (hH : ContDiff ℝ ∞ (Function.uncurry H)) (hK : HasCompactSupport (Function.uncurry H)) (t : ℝ) :
    ∃ Φ : E n ≃ₜ E n, (⇑Φ=Return.flow (Problem.hamVF H) t) ∧
      ContDiff ℝ ∞ Φ ∧ ContDiff ℝ ∞ Φ.symm ∧
      ∀ x v w,Problem.omega0 (fderiv ℝ Φ x v) (fderiv ℝ Φ x w)=Problem.omega0 v w := by
  have hV := compact_hamiltonian_csField hH hK
  obtain ⟨Φ,hΦ,hΦi,_,_,hω,hsol⟩ := exists_hamiltonian_endpoint omega0L_isInvertible
    (fun v w => omega0_skew v w) hH.neg hK.neg 0 t
  have he : ⇑Φ=Return.flow (Problem.hamVF H) t := by
    funext x
    have hh := hsol (fun s => Return.flow (Problem.hamVF H) s x)
      (hV.flowFrom_continuous 0 x) (fun s => by
        change HasDerivAt (fun s => Return.flow (Problem.hamVF H) s x)
          (hamiltonianField omega0L (fun q : ℝ × E n => -H q.1 q.2)
            (s,Return.flow (Problem.hamVF H) s x)) s
        rw [←problemField_eq_negative_hamiltonianField hH]
        exact hV.flow_hasDerivAt x s)
    simpa only [zero_add,hV.flow_zero] using hh
  exact ⟨Φ,he,hΦ,hΦi,hω⟩

/-- The prescribed source isotopy is the global flow at every real time. -/
theorem ofIsotopy_flow_global {k : ℕ} {F : Fin k → ℝ → E n → E n}
    {s : Fin k → E n} {r1 r2 r3 ρ : Fin k → ℝ} (hF : CommonIsotopy F s r1 r2 r3 ρ)
    (i : Fin k) (u : E n) (hu : ‖u‖<r1 i) (t : ℝ) :
    Return.flow (Problem.hamVF (ofIsotopy F r1 r2 r3)) t (s i+u)=F i t u := by
  obtain ⟨S,hS⟩ := hF.bounded
  have hcompact := hasCompactSupport_of_space_time (isCompact_closedBall (0:E n) S)
    (ofIsotopy_support hS) (fun t x ht => ofIsotopy_eq_zero_of_time hF ht x)
  have hV := compact_hamiltonian_csField (ofIsotopy_smooth hF) hcompact
  apply hV.flowFrom_eq (t:=t)
  refine ⟨hF.start i u,?_⟩
  intro r
  have huρ : u∈ball (0:E n) (ρ i) := by
    obtain ⟨_,h12,h23,h3ρ⟩ := hF.radii i
    exact mem_ball_zero_iff.mpr (by linarith)
  have hd := hasDerivAt_time ((hF.sympFamily i).differentiableAt (s:=r) huρ)
  rw [hamVF_ofIsotopy_image hF i r hu,hd.deriv]
  exact hd

end SymplecticPacking.General.Ham
