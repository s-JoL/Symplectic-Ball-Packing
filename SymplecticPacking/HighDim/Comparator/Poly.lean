import SymplecticPacking.HighDim.Comparator.Rearrangement

/-!
# Convex piecewise-affine functions as finite data

A `PolyFn m` is a finite list of affine functions; its value is their maximum. The comparator
iteration acts on this data: sums, nonnegative multiples and the rearrangement `R_j`, the latter
by Fourier–Motzkin elimination of the slice variable `a` from the epigraph system
(paper lem:cmp-rearrangement, polyhedral part).
-/

noncomputable section

namespace SymplecticPacking.HighDim

open Set
open OAI.PackingSufficiencySupport.MomentPolytope (Moments region)

variable {m q : ℕ}

/-- An affine function `p ↦ ⟨coef, p⟩ + const`. -/
structure AffinePiece (m : ℕ) where
  coef : Fin m → ℝ
  const : ℝ

namespace AffinePiece

def eval (a : AffinePiece m) (p : Moments m) : ℝ := ∑ j, a.coef j * p j + a.const

instance : Add (AffinePiece m) := ⟨fun a b => ⟨a.coef + b.coef, a.const + b.const⟩⟩

def smul (c : ℝ) (a : AffinePiece m) : AffinePiece m := ⟨c • a.coef, c * a.const⟩

@[simp] theorem eval_add (a b : AffinePiece m) (p : Moments m) :
    (a + b).eval p = a.eval p + b.eval p := by
  change ∑ j, (a.coef j + b.coef j) * p j + (a.const + b.const) = _
  simp only [eval, add_mul, Finset.sum_add_distrib]
  ring

@[simp] theorem eval_smul (c : ℝ) (a : AffinePiece m) (p : Moments m) :
    (a.smul c).eval p = c * a.eval p := by
  simp only [eval, smul, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum, mul_assoc]

theorem eval_affine (a : AffinePiece m) : ConvexOn ℝ univ a.eval ∧ ConcaveOn ℝ univ a.eval := by
  have hl : IsLinearMap ℝ (fun p : Moments m => ∑ j, a.coef j * p j) := by
    constructor
    · intro x y; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    · intro c x; simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
  let L : Moments m →ₗ[ℝ] ℝ := hl.mk'
  have : a.eval = fun p => L p + a.const := rfl
  rw [this]
  exact ⟨(L.convexOn convex_univ).add (convexOn_const _ convex_univ),
    (L.concaveOn convex_univ).add (concaveOn_const _ convex_univ)⟩

/-- `p ↦ ℓ(update p j 0)`: the `j`-th coefficient set to `0`. -/
def zeroAt (j : Fin m) (a : AffinePiece m) : AffinePiece m :=
  ⟨Function.update a.coef j 0, a.const⟩

theorem sum_mul_update (c p : Moments m) (j : Fin m) (t : ℝ) :
    ∑ i, c i * Function.update p j t i = ∑ i, c i * p i + c j * (t - p j) := by
  classical
  have : ∀ i, c i * Function.update p j t i =
      c i * p i + (if i = j then c j * (t - p j) else 0) := by
    intro i
    by_cases hij : i = j
    · subst hij; simp; ring
    · simp [hij]
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib]
  simp

theorem sum_update_mul (c p : Moments m) (j : Fin m) (s : ℝ) :
    ∑ i, Function.update c j s i * p i = ∑ i, c i * p i + (s - c j) * p j := by
  classical
  have : ∀ i, Function.update c j s i * p i =
      c i * p i + (if i = j then (s - c j) * p j else 0) := by
    intro i
    by_cases hij : i = j
    · subst hij; simp; ring
    · simp [hij]
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_add_distrib]
  simp

/-- On the line through `p` in direction `j`, a piece is affine with slope `coef j`. -/
theorem eval_update (a : AffinePiece m) (j : Fin m) (p : Moments m) (t : ℝ) :
    a.eval (Function.update p j t) = a.coef j * t + (a.zeroAt j).eval p := by
  simp only [eval, zeroAt, sum_mul_update, sum_update_mul]
  ring

theorem eval_update_add (a : AffinePiece m) (j : Fin m) (p : Moments m) (t : ℝ) :
    a.eval (Function.update p j (t + p j)) = a.coef j * t + a.eval p := by
  simp only [eval, sum_mul_update]
  ring

end AffinePiece

/-- A convex piecewise-affine function: the maximum of a finite nonempty list of affine
functions (the empty list denotes `0`). -/
abbrev PolyFn (m : ℕ) := List (AffinePiece m)

namespace PolyFn

/-- `max_r ℓ_r(p)`. -/
def eval : PolyFn m → Moments m → ℝ
  | [] => fun _ => 0
  | a :: l => fun p => l.foldl (fun acc b => max acc (b.eval p)) (a.eval p)

/-- The constant function. -/
def const (c : ℝ) : PolyFn m := [⟨0, c⟩]

/-- Pointwise sum: all pairwise sums of pieces. -/
def add (F G : PolyFn m) : PolyFn m := F.flatMap fun a => G.map fun b => a + b

/-- Multiplication by `c ≥ 0`. -/
def smul (c : ℝ) (F : PolyFn m) : PolyFn m := F.map (AffinePiece.smul c)

/-! ### Data for the rearrangement

On the line through `p` in direction `j`, a piece `r` gives two affine functions of the slice
variable `a`: `a ↦ r(update p j a) = c·a + r⁰(p)` and `a ↦ r(update p j (a + p_j)) = c·a + r(p)`,
with `c = r.coef j` and `r⁰ = r.zeroAt j`. These are the `slices` (slope, intercept). Minimising the
maximum of the slices over `a ∈ [0, H(p)]`, `H = L_j − p_j = min_ν h_ν`, eliminates `a`
(Fourier–Motzkin): the minimum is the maximum of the intercepts of slices of slope `≥ 0`, the
values at `a = h_ν` of slices of negative slope, and the zero-slope convex combinations of a
positive-slope and a negative-slope slice. -/

/-- The slices `(slope, intercept)` of the pieces in direction `j`. -/
def slices (j : Fin m) (F : PolyFn m) : List (ℝ × AffinePiece m) :=
  F.flatMap fun r => [(r.coef j, r.zeroAt j), (r.coef j, r)]

/-- `h_ν(p) = (ℓ_ν − Σ_{i≠j} b_{νi} p_i)/b_{νj} − p_j`. -/
def hiPiece (Δ : Polytope m q) (j : Fin m) (ν : Fin q) : AffinePiece m :=
  ⟨fun i => if i = j then -1 else -(Δ.b ν i / Δ.b ν j), Δ.ℓ ν / Δ.b ν j⟩

/-- The faces bounding direction `j`. -/
def faces (Δ : Polytope m q) (j : Fin m) : List (Fin q) :=
  (List.finRange q).filter fun ν => decide (0 < Δ.b ν j)

/-- The pieces `h_ν` over the faces bounding direction `j`, so that `H = min_ν h_ν`; the
placeholder `0` when there is no such face (excluded by `Polytope.Spec`). -/
def hiData (Δ : Polytope m q) (j : Fin m) : List (AffinePiece m) :=
  match (faces Δ j).map (hiPiece Δ j) with
  | [] => [⟨0, 0⟩]
  | a :: l => a :: l

/-- The zero-slope combination `(α_k B_l − α_l B_k)/(α_k − α_l)` of two slices. -/
def pairPiece (k l : ℝ × AffinePiece m) : AffinePiece m :=
  (l.2.smul k.1 + k.2.smul (-l.1)).smul (1 / (k.1 - l.1))

/-- Values at `a = 0` of the slices of slope `≥ 0`. -/
def rearrLo (j : Fin m) (F : PolyFn m) : PolyFn m :=
  ((slices j F).filter fun k => decide (0 ≤ k.1)).map Prod.snd

/-- Values at `a = h_ν` of the slices of negative slope. -/
def rearrHi (Δ : Polytope m q) (j : Fin m) (F : PolyFn m) : PolyFn m :=
  ((slices j F).filter fun k => decide (k.1 < 0)).flatMap fun k =>
    (hiData Δ j).map fun h => k.2 + h.smul k.1

/-- Zero-slope combinations of a positive-slope and a negative-slope slice. -/
def rearrPair (j : Fin m) (F : PolyFn m) : PolyFn m :=
  ((slices j F).filter fun k => decide (0 < k.1)).flatMap fun k =>
    ((slices j F).filter fun l => decide (l.1 < 0)).map fun l => pairPiece k l

/-- `R_j` on data: Fourier–Motzkin elimination of the slice variable from the epigraph
system `a ≥ 0`, `x ≥ 0`, `b_{νj}(a+x) + Σ_{i≠j} b_{νi}y_i ≤ ℓ_ν`, `t ≥ ℓ_r(y,a)`,
`t ≥ ℓ_r(y,a+x)`; the lower envelope of `t` is again a maximum of affine functions on `Δ`. -/
def rearr (Δ : Polytope m q) (j : Fin m) (F : PolyFn m) : PolyFn m :=
  rearrLo j F ++ rearrHi Δ j F ++ rearrPair j F

/-- `ℛ` on data. -/
def rearrAll (Δ : Polytope m q) (F : PolyFn m) : PolyFn m :=
  (List.finRange m).foldl (fun G j => rearr Δ j G) F

theorem eval_const (c : ℝ) (p : Moments m) : eval (const c : PolyFn m) p = c := by
  simp [eval, const, AffinePiece.eval]

section fold

variable (p : Moments m)

/-- The fold step. -/
abbrev step (acc : ℝ) (b : AffinePiece m) : ℝ := max acc (b.eval p)

theorem le_foldl (l : PolyFn m) (x : ℝ) : x ≤ l.foldl (step p) x := by
  induction l generalizing x with
  | nil => exact le_rfl
  | cons b l ih => exact (le_max_left _ _).trans (ih _)

theorem mem_le_foldl {l : PolyFn m} {b : AffinePiece m} (hb : b ∈ l) (x : ℝ) :
    b.eval p ≤ l.foldl (step p) x := by
  induction l generalizing x with
  | nil => simp at hb
  | cons c l ih =>
    rcases List.mem_cons.mp hb with rfl | hb
    · exact (le_max_right _ _).trans (le_foldl p l _)
    · exact ih hb _

theorem foldl_le {l : PolyFn m} {x M : ℝ} (hx : x ≤ M) (hl : ∀ b ∈ l, b.eval p ≤ M) :
    l.foldl (step p) x ≤ M := by
  induction l generalizing x with
  | nil => exact hx
  | cons c l ih =>
    exact ih (max_le hx (hl c (List.mem_cons_self ..)))
      (fun b hb => hl b (List.mem_cons_of_mem _ hb))

theorem foldl_eq (l : PolyFn m) (x : ℝ) :
    l.foldl (step p) x = x ∨ ∃ b ∈ l, l.foldl (step p) x = b.eval p := by
  induction l generalizing x with
  | nil => exact Or.inl rfl
  | cons c l ih =>
    rcases ih (max x (c.eval p)) with h | ⟨b, hb, h⟩
    · have e : (c :: l).foldl (step p) x = max x (c.eval p) := h
      rcases max_choice x (c.eval p) with h' | h'
      · exact Or.inl (e.trans h')
      · exact Or.inr ⟨c, List.mem_cons_self .., e.trans h'⟩
    · exact Or.inr ⟨b, List.mem_cons_of_mem _ hb, h⟩

end fold

/-- Values of the pieces are below the maximum. -/
theorem le_eval {F : PolyFn m} {a : AffinePiece m} (ha : a ∈ F) (p : Moments m) :
    a.eval p ≤ eval F p := by
  cases F with
  | nil => simp at ha
  | cons c l =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_foldl p l _
    · exact mem_le_foldl p ha _

theorem eval_le {F : PolyFn m} (hF : F ≠ []) {p : Moments m} {M : ℝ}
    (h : ∀ a ∈ F, a.eval p ≤ M) : eval F p ≤ M := by
  cases F with
  | nil => exact absurd rfl hF
  | cons c l =>
    exact foldl_le p (h c (List.mem_cons_self ..)) (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- The maximum is attained. -/
theorem eval_mem {F : PolyFn m} (hF : F ≠ []) (p : Moments m) :
    ∃ a ∈ F, eval F p = a.eval p := by
  cases F with
  | nil => exact absurd rfl hF
  | cons c l =>
    rcases foldl_eq p l (c.eval p) with h | ⟨b, hb, h⟩
    · exact ⟨c, List.mem_cons_self .., h⟩
    · exact ⟨b, List.mem_cons_of_mem _ hb, h⟩

theorem add_ne_nil {F G : PolyFn m} (hF : F ≠ []) (hG : G ≠ []) : add F G ≠ [] := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil F hF
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil G hG
  exact List.ne_nil_of_mem (List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩)

theorem eval_add {F G : PolyFn m} (hF : F ≠ []) (hG : G ≠ []) (p : Moments m) :
    eval (add F G) p = eval F p + eval G p := by
  apply le_antisymm
  · refine eval_le (add_ne_nil hF hG) fun c hc => ?_
    obtain ⟨a, ha, hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    rw [AffinePiece.eval_add]
    exact add_le_add (le_eval ha p) (le_eval hb p)
  · obtain ⟨a, ha, hFa⟩ := eval_mem hF p
    obtain ⟨b, hb, hGb⟩ := eval_mem hG p
    rw [hFa, hGb, ← AffinePiece.eval_add]
    exact le_eval (List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩) p

theorem smul_ne_nil {F : PolyFn m} (hF : F ≠ []) (c : ℝ) : smul c F ≠ [] := by
  simpa [smul] using hF

theorem eval_smul {F : PolyFn m} {c : ℝ} (hc : 0 ≤ c) (p : Moments m) :
    eval (smul c F) p = c * eval F p := by
  by_cases hF : F = []
  · subst hF; simp [smul, eval]
  apply le_antisymm
  · refine eval_le (smul_ne_nil hF c) fun b hb => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    rw [AffinePiece.eval_smul]
    exact mul_le_mul_of_nonneg_left (le_eval ha p) hc
  · obtain ⟨a, ha, hFa⟩ := eval_mem hF p
    rw [hFa, ← AffinePiece.eval_smul]
    exact le_eval (List.mem_map.mpr ⟨a, ha, rfl⟩) p

theorem eval_convexOn (F : PolyFn m) : ConvexOn ℝ univ (eval F) := by
  by_cases hF : F = []
  · subst hF; exact convexOn_const 0 convex_univ
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain ⟨c, hc, he⟩ := eval_mem hF (a • x + b • y)
  rw [he]
  have := (c.eval_affine.1).2 (mem_univ x) (mem_univ y) ha hb hab
  refine this.trans ?_
  simp only [smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (le_eval hc x) ha)
    (mul_le_mul_of_nonneg_left (le_eval hc y) hb)

theorem affine_continuous (a : AffinePiece m) : Continuous a.eval := by
  unfold AffinePiece.eval
  fun_prop

theorem eval_continuous (F : PolyFn m) : Continuous (eval F) := by
  cases F with
  | nil => exact continuous_const
  | cons c l =>
    show Continuous fun p => l.foldl (step p) (c.eval p)
    have key : ∀ (l : PolyFn m) (x : Moments m → ℝ), Continuous x →
        Continuous fun p => l.foldl (step p) (x p) := by
      intro l
      induction l with
      | nil => exact fun x hx => hx
      | cons b l ih => exact fun x hx => ih _ (hx.max (affine_continuous b))
    exact key l _ (affine_continuous c)

/-! ### Correctness of the data rearrangement -/

theorem mem_slices {j : Fin m} {F : PolyFn m} {k : ℝ × AffinePiece m} :
    k ∈ slices j F ↔ ∃ r ∈ F, k = (r.coef j, r.zeroAt j) ∨ k = (r.coef j, r) := by
  simp [slices]

theorem mem_rearr {Δ : Polytope m q} {j : Fin m} {F : PolyFn m} {a : AffinePiece m} :
    a ∈ rearr Δ j F ↔
      (∃ k ∈ slices j F, 0 ≤ k.1 ∧ k.2 = a) ∨
      (∃ k ∈ slices j F, k.1 < 0 ∧ ∃ h ∈ hiData Δ j, k.2 + h.smul k.1 = a) ∨
      (∃ k ∈ slices j F, 0 < k.1 ∧ ∃ l ∈ slices j F, l.1 < 0 ∧ pairPiece k l = a) := by
  simp only [rearr, rearrLo, rearrHi, rearrPair, List.mem_append, List.mem_map,
    List.mem_flatMap, List.mem_filter, decide_eq_true_eq, and_assoc, or_assoc]

theorem hiData_ne_nil (Δ : Polytope m q) (j : Fin m) : hiData Δ j ≠ [] := by
  unfold hiData
  split <;> simp

theorem hiData_eq {Δ : Polytope m q} (hΔ : Δ.Spec) (j : Fin m) :
    hiData Δ j = (faces Δ j).map (hiPiece Δ j) := by
  obtain ⟨ν, hν⟩ := hΔ.bounded_dir j
  have hmem : hiPiece Δ j ν ∈ (faces Δ j).map (hiPiece Δ j) :=
    List.mem_map.mpr ⟨ν, by simp [faces, hν], rfl⟩
  unfold hiData
  split
  · rename_i h
    rw [h] at hmem
    simp at hmem
  · rename_i h
    exact h.symm

theorem hiPiece_eval (Δ : Polytope m q) (j : Fin m) {ν : Fin q} (hν : 0 < Δ.b ν j)
    (p : Moments m) :
    (hiPiece Δ j ν).eval p =
      (Δ.ℓ ν - ∑ i, (if i = j then 0 else Δ.b ν i * p i)) / Δ.b ν j - p j := by
  have : ∀ i, (if i = j then (-1 : ℝ) else -(Δ.b ν i / Δ.b ν j)) * p i =
      -((if i = j then 0 else Δ.b ν i * p i) / Δ.b ν j) - (if i = j then p j else 0) := by
    intro i
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]; ring
  simp only [AffinePiece.eval, hiPiece]
  rw [Finset.sum_congr rfl fun i _ => this i, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.sum_div]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp
  ring

/-- Every `h_ν` is at least `H = L_j − p_j`. -/
theorem le_hiData {Δ : Polytope m q} (hΔ : Δ.Spec) (j : Fin m) (p : Moments m)
    {h : AffinePiece m} (hh : h ∈ hiData Δ j) : Δ.sliceLen j p - p j ≤ h.eval p := by
  rw [hiData_eq hΔ] at hh
  obtain ⟨ν, hν, rfl⟩ := List.mem_map.mp hh
  have hb : 0 < Δ.b ν j := by simpa [faces] using hν
  rw [hiPiece_eval Δ j hb]
  have hL : Δ.sliceLen j p ≤ (Δ.ℓ ν - ∑ i, (if i = j then 0 else Δ.b ν i * p i)) / Δ.b ν j :=
    ciInf_le (Set.finite_range _).bddBelow (⟨ν, hb⟩ : {ν : Fin q // 0 < Δ.b ν j})
  linarith

/-- Some `h_ν` equals `H = L_j − p_j`. -/
theorem exists_hiData {Δ : Polytope m q} (hΔ : Δ.Spec) (j : Fin m) (p : Moments m) :
    ∃ h ∈ hiData Δ j, h.eval p = Δ.sliceLen j p - p j := by
  obtain ⟨ν₀, hν₀⟩ := hΔ.bounded_dir j
  have : Nonempty {ν : Fin q // 0 < Δ.b ν j} := ⟨⟨ν₀, hν₀⟩⟩
  obtain ⟨ν, hν⟩ := Finite.exists_min (fun ν : {ν : Fin q // 0 < Δ.b ν j} =>
    (Δ.ℓ ν - ∑ i, (if i = j then 0 else Δ.b ν i * p i)) / Δ.b ν j)
  refine ⟨hiPiece Δ j ν, ?_, ?_⟩
  · rw [hiData_eq hΔ]
    exact List.mem_map.mpr ⟨ν, by simp [faces, ν.2], rfl⟩
  · rw [hiPiece_eval Δ j ν.2]
    have : Δ.sliceLen j p = (Δ.ℓ ν - ∑ i, (if i = j then 0 else Δ.b ν i * p i)) / Δ.b ν j :=
      le_antisymm (ciInf_le (Set.finite_range _).bddBelow ν) (le_ciInf hν)
    rw [this]

/-- A slice lies below the integrand of `R_j`. -/
theorem slice_le {j : Fin m} {F : PolyFn m} {k : ℝ × AffinePiece m} (hk : k ∈ slices j F)
    (p : Moments m) (t : ℝ) :
    k.1 * t + k.2.eval p ≤
      max (eval F (Function.update p j t)) (eval F (Function.update p j (t + p j))) := by
  obtain ⟨r, hr, rfl | rfl⟩ := mem_slices.mp hk
  · have := le_eval hr (Function.update p j t)
    rw [AffinePiece.eval_update] at this
    exact this.trans (le_max_left _ _)
  · have := le_eval hr (Function.update p j (t + p j))
    rw [AffinePiece.eval_update_add] at this
    exact this.trans (le_max_right _ _)

/-- The integrand of `R_j` is the maximum of the slices. -/
theorem integrand_le {j : Fin m} {F : PolyFn m} (hF : F ≠ []) (p : Moments m) (t V : ℝ)
    (h : ∀ k ∈ slices j F, k.1 * t + k.2.eval p ≤ V) :
    max (eval F (Function.update p j t)) (eval F (Function.update p j (t + p j))) ≤ V :=
  max_le
    (eval_le hF fun r hr => by
      rw [AffinePiece.eval_update]; exact h _ (mem_slices.mpr ⟨r, hr, Or.inl rfl⟩))
    (eval_le hF fun r hr => by
      rw [AffinePiece.eval_update_add]; exact h _ (mem_slices.mpr ⟨r, hr, Or.inr rfl⟩))

theorem eval_hi (k : ℝ × AffinePiece m) (h : AffinePiece m) (p : Moments m) :
    (k.2 + h.smul k.1).eval p = k.2.eval p + k.1 * h.eval p := by
  simp

theorem eval_pair (k l : ℝ × AffinePiece m) (p : Moments m) :
    (pairPiece k l).eval p = (k.1 * l.2.eval p - l.1 * k.2.eval p) / (k.1 - l.1) := by
  simp only [pairPiece, AffinePiece.eval_smul, AffinePiece.eval_add]
  ring

theorem rearr_ne_nil {Δ : Polytope m q} (j : Fin m) {F : PolyFn m} (hF : F ≠ []) :
    rearr Δ j F ≠ [] := by
  obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil F hF
  have hk : (r.coef j, r) ∈ slices j F := mem_slices.mpr ⟨r, hr, Or.inr rfl⟩
  obtain ⟨h, hh⟩ := List.exists_mem_of_ne_nil _ (hiData_ne_nil Δ j)
  rcases le_or_gt 0 (r.coef j) with hc | hc
  · exact List.ne_nil_of_mem (mem_rearr.mpr (Or.inl ⟨_, hk, hc, rfl⟩))
  · exact List.ne_nil_of_mem (mem_rearr.mpr (Or.inr (Or.inl ⟨_, hk, hc, h, hh, rfl⟩)))

/-- The data rearrangement computes `R_j`. -/
theorem rearr_eval {Δ : Polytope m q} (hΔ : Δ.Spec) (j : Fin m) {F : PolyFn m}
    (hF : F ≠ []) : EqOn (eval (rearr Δ j F)) (HighDim.rearr Δ j (eval F)) Δ.set := by
  intro p hp
  have hH0 : 0 ≤ Δ.sliceLen j p - p j := by
    have := Polytope.le_sliceLen hΔ hp j; linarith
  have hne := rearr_ne_nil (Δ := Δ) j hF
  set V := eval (rearr Δ j F) p with hV
  -- every output piece is a lower bound for the integrand
  have lower : ∀ a : Icc (0 : ℝ) (Δ.sliceLen j p - p j),
      V ≤ rearrIntegrand Δ j (eval F) p a := by
    intro a
    show V ≤ max (eval F (Function.update p j a)) (eval F (Function.update p j (a + p j)))
    have ha0 : (0 : ℝ) ≤ a := a.2.1
    have haH : (a : ℝ) ≤ Δ.sliceLen j p - p j := a.2.2
    refine eval_le hne fun b hb => ?_
    rcases mem_rearr.mp hb with ⟨k, hk, hk0, rfl⟩ | ⟨k, hk, hk0, h, hh, rfl⟩ |
        ⟨k, hk, hk0, l, hl, hl0, rfl⟩
    · have h1 := slice_le hk p a
      have h2 := mul_nonneg hk0 ha0
      linarith
    · rw [eval_hi]
      have h1 := le_hiData hΔ j p hh
      have h2 := slice_le hk p a
      have h3 := mul_le_mul_of_nonpos_left (haH.trans h1) hk0.le
      linarith
    · rw [eval_pair, div_le_iff₀ (by linarith)]
      have h1 := mul_le_mul_of_nonneg_left (slice_le hl p a) hk0.le
      have h2 := mul_le_mul_of_nonneg_left (slice_le hk p a) (neg_nonneg.mpr hl0.le)
      nlinarith
  have : Nonempty (Icc (0 : ℝ) (Δ.sliceLen j p - p j)) := ⟨⟨0, le_rfl, hH0⟩⟩
  have hbdd : BddBelow (Set.range (rearrIntegrand Δ j (eval F) p)) :=
    ⟨V, by rintro _ ⟨a, rfl⟩; exact lower a⟩
  rw [rearr_eq_iInf]
  refine le_antisymm (le_ciInf lower) ?_
  -- the output pieces, as inequalities
  have hlo : ∀ k ∈ slices j F, 0 ≤ k.1 → k.2.eval p ≤ V := fun k hk hk0 =>
    le_eval (mem_rearr.mpr (Or.inl ⟨k, hk, hk0, rfl⟩)) p
  have hhi : ∀ k ∈ slices j F, k.1 < 0 → ∀ h ∈ hiData Δ j,
      k.2.eval p + k.1 * h.eval p ≤ V := fun k hk hk0 h hh => by
    rw [← eval_hi]
    exact le_eval (mem_rearr.mpr (Or.inr (Or.inl ⟨k, hk, hk0, h, hh, rfl⟩))) p
  have hpr : ∀ k ∈ slices j F, 0 < k.1 → ∀ l ∈ slices j F, l.1 < 0 →
      (k.1 * l.2.eval p - l.1 * k.2.eval p) / (k.1 - l.1) ≤ V := fun k hk hk0 l hl hl0 => by
    rw [← eval_pair]
    exact le_eval (mem_rearr.mpr (Or.inr (Or.inr ⟨k, hk, hk0, l, hl, hl0, rfl⟩))) p
  -- the minimiser: the largest of `0` and the lower constraints `(V − β_l)/α_l`, `α_l < 0`
  let N : Finset ℝ := insert 0 (((slices j F).filter fun l => decide (l.1 < 0)).map
    (fun l => (V - l.2.eval p) / l.1)).toFinset
  have hN : N.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  set A := N.max' hN with hAdef
  have hA0 : 0 ≤ A := N.le_max' 0 (Finset.mem_insert_self _ _)
  have hAl : ∀ l ∈ slices j F, l.1 < 0 → (V - l.2.eval p) / l.1 ≤ A := fun l hl hl0 =>
    N.le_max' _ (Finset.mem_insert_of_mem (List.mem_toFinset.mpr
      (List.mem_map.mpr ⟨l, List.mem_filter.mpr ⟨hl, by simpa using hl0⟩, rfl⟩)))
  have hAcase : A = 0 ∨ ∃ l ∈ slices j F, l.1 < 0 ∧ A = (V - l.2.eval p) / l.1 := by
    rcases Finset.mem_insert.mp (N.max'_mem hN) with h | h
    · exact Or.inl h
    · obtain ⟨l, hl, he⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
      obtain ⟨hl, hl0⟩ := List.mem_filter.mp hl
      exact Or.inr ⟨l, hl, by simpa using hl0, he.symm⟩
  have hAH : A ≤ Δ.sliceLen j p - p j := by
    rcases hAcase with h | ⟨l, hl, hl0, h⟩
    · rw [h]; exact hH0
    · obtain ⟨g, hg, he⟩ := exists_hiData hΔ j p
      have := hhi l hl hl0 g hg
      rw [he] at this
      rw [h, div_le_iff_of_neg hl0]
      linarith
  have hall : ∀ k ∈ slices j F, k.1 * A + k.2.eval p ≤ V := by
    intro k hk
    rcases lt_trichotomy k.1 0 with hk0 | hk0 | hk0
    · have := hAl k hk hk0
      rw [div_le_iff_of_neg hk0] at this
      linarith
    · rw [hk0, zero_mul, zero_add]
      exact hlo k hk hk0.ge
    · rcases hAcase with h | ⟨l, hl, hl0, h⟩
      · rw [h, mul_zero, zero_add]
        exact hlo k hk hk0.le
      · have hp' := hpr k hk hk0 l hl hl0
        rw [div_le_iff₀ (by linarith)] at hp'
        have hA : A * l.1 = V - l.2.eval p := by rw [h, div_mul_cancel₀ _ hl0.ne]
        have e : k.1 * (A * l.1) = k.1 * (V - l.2.eval p) := by rw [hA]
        nlinarith [mul_pos hk0 (neg_pos.mpr hl0)]
  exact (ciInf_le hbdd ⟨A, hA0, hAH⟩).trans (integrand_le hF p A V hall)

theorem rearrAll_ne_nil {Δ : Polytope m q} {F : PolyFn m} (hF : F ≠ []) :
    rearrAll Δ F ≠ [] := by
  unfold rearrAll
  generalize List.finRange m = l
  induction l generalizing F with
  | nil => exact hF
  | cons j l ih => exact ih (rearr_ne_nil j hF)

theorem const_ne_nil (c : ℝ) : (const c : PolyFn m) ≠ [] := List.cons_ne_nil _ _

theorem rearrAll_eval {Δ : Polytope m q} (hΔ : Δ.Spec) {F : PolyFn m} (hF : F ≠ []) :
    EqOn (eval (rearrAll Δ F)) (HighDim.rearrAll Δ (eval F)) Δ.set := by
  unfold rearrAll HighDim.rearrAll
  generalize List.finRange m = l
  induction l generalizing F with
  | nil => exact fun _ _ => rfl
  | cons j l ih =>
    simp only [List.foldl_cons]
    refine (ih (rearr_ne_nil j hF)).trans ?_
    exact rearrList_congr hΔ l (rearr_eval hΔ j hF)

end PolyFn

end SymplecticPacking.HighDim
