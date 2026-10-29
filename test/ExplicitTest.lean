import SymplecticPacking.Explicit
open SymplecticPacking.Explicit

/-! Whitelist names are matched on declaration boundaries. -/
#guard reviewedNameMatches "Filter.lim" "Filter.lim"
#guard reviewedNameMatches "Filter.lim" "Filter.lim._proof_1"
#guard !(reviewedNameMatches "Filter.lim" "Filter.limsup")
#guard !(reviewedNameMatches "ContinuousLinearMap.inverse"
    "ContinuousLinearMap.inverseArbitrary")
#guard reviewedNameMatches "definition._@.Mathlib.Analysis.InnerProductSpace.PiL2."
    "definition._@.Mathlib.Analysis.InnerProductSpace.PiL2.someAuxiliary"

/-! ## Accepted and rejected definitions -/
noncomputable def good (x : ℝ) : ℝ := Real.sqrt (x ^ 2 + 1) + Real.exp x + deriv Real.sin x
noncomputable def viaThe : ℝ := the (P := fun y : ℝ => y = 2) ⟨2, rfl, fun _ h => h⟩
noncomputable def bad : ℝ := Classical.choose (⟨0, le_refl 0⟩ : ∃ y : ℝ, y ≤ 0)
#check_explicit viaThe
#check_explicit good
#check_explicit_rejects bad

/- Proof-valued local declarations do not determine the returned data. A local
data declaration remains subject to the same audit as a direct choice. -/
noncomputable def proofLet (x : ℝ) : ℝ :=
  have h : ∃ y : ℝ, y ≤ 0 := by
    exact ⟨bad, Classical.choose_spec (⟨0, le_refl 0⟩ : ∃ y : ℝ, y ≤ 0)⟩
  let _proof : True := by obtain ⟨y, hy⟩ := h; trivial
  x + 1
noncomputable def dataLet : ℝ :=
  let y : ℝ := bad
  y + 1
#check_explicit proofLet
#check_explicit_rejects dataLet

/-! ## Searches -/

namespace ExplicitSearchTest

/-- Classical `if` on a real comparison inside a formula: still accepted. -/
noncomputable def realIf (x : ℝ) : ℝ := open Classical in if x < 1 then x else 1 - x
#check_explicit realIf

/-- An enumeration of (time-dependent) Hamiltonians on `ℝ⁴`. -/
noncomputable def enumH (n : ℕ) : ℝ → (Fin 4 → ℝ) → ℝ := fun _ x => (n : ℝ) * x 0 ^ 2

/-- A `Prop` specification of Hamiltonians (not decidable). -/
def HSpec (H : ℝ → (Fin 4 → ℝ) → ℝ) : Prop := ∀ t x, H t x ≤ x 0 ^ 2

theorem good0 : HSpec (enumH 0) := fun _ x => by simp [enumH]; positivity

theorem exists_good : ∃ n, HSpec (enumH n) := ⟨0, good0⟩

/-- (a) "least `n` such that the `n`-th enumerated Hamiltonian satisfies the spec", via
`Nat.find` with classical decidability: REJECTED. -/
noncomputable def leastGoodIndex : ℕ := open Classical in Nat.find exists_good
noncomputable def searchedH : ℝ → (Fin 4 → ℝ) → ℝ := enumH leastGoodIndex
#check_explicit_rejects leastGoodIndex
#check_explicit_rejects searchedH

/-- (a') the same search hidden behind a wrapper taking the instance as a parameter. -/
def myFind (p : ℕ → Prop) [DecidablePred p] (h : ∃ n, p n) : ℕ := Nat.find h
noncomputable def searchedH' : ℝ → (Fin 4 → ℝ) → ℝ :=
  enumH (open Classical in myFind (fun n => HSpec (enumH n)) exists_good)
#check_explicit_rejects searchedH'

/-- (a'') the same search as a definite description of the least index over `ℕ`. -/
theorem existsUnique_least : ∃! n, HSpec (enumH n) ∧ ∀ m < n, ¬ HSpec (enumH m) := by
  classical
  exact ⟨Nat.find exists_good, ⟨Nat.find_spec exists_good, fun m hm => Nat.find_min _ hm⟩,
    fun y ⟨hy, hmin⟩ => le_antisymm (not_lt.1 fun h => hmin _ h (Nat.find_spec exists_good))
      (Nat.find_min' _ hy)⟩
noncomputable def searchedH'' : ℝ → (Fin 4 → ℝ) → ℝ := enumH (the existsUnique_least)
#check_explicit_rejects searchedH''

/-- (a''-pair) the same search wrapped as the unique pair `(n, 0) : ℕ × ℝ`, then projected:
REJECTED (definite description over a type with a discrete factor). -/
theorem existsUnique_leastPair :
    ∃! x : ℕ × ℝ, (HSpec (enumH x.1) ∧ ∀ m < x.1, ¬ HSpec (enumH m)) ∧ x.2 = 0 := by
  obtain ⟨n, hn, huniq⟩ := existsUnique_least
  exact ⟨(n, 0), ⟨hn, rfl⟩, fun y hy => Prod.ext (huniq _ hy.1) hy.2⟩
noncomputable def leastPair : ℕ × ℝ := the existsUnique_leastPair
noncomputable def searchedPairH : ℝ → (Fin 4 → ℝ) → ℝ := enumH leastPair.1
#check_explicit_rejects leastPair
#check_explicit_rejects searchedPairH

/-- (a''') least index via `WellFounded.min` on a set of naturals. -/
noncomputable def searchedH''' : ℝ → (Fin 4 → ℝ) → ℝ :=
  enumH (WellFounded.min Nat.lt_wfRel.wf {n | HSpec (enumH n)} exists_good)
#check_explicit_rejects searchedH'''

/-- (a'''') least-element search over a function type (not a search type). -/
noncomputable def overFunctions : ℕ → ℕ :=
  WellFounded.min (InvImage.wf (fun f : ℕ → ℕ => f 0) Nat.lt_wfRel.wf) {f | f 0 = 3}
    ⟨fun _ => 3, rfl⟩
#check_explicit_rejects overFunctions

open Classical in
/-- (a5) least element of a classically filtered finset. -/
noncomputable def viaFilter : ℕ :=
  ((Finset.range 5).filter (fun n => HSpec (enumH n))).min'
    ⟨0, Finset.mem_filter.2 ⟨by simp, good0⟩⟩
#check_explicit_rejects viaFilter

/-- (a6) least index via `sInf` on `ℕ` (Mathlib's `Nat.find` with `Classical.decPred`). -/
noncomputable def viaSInf : ℝ → (Fin 4 → ℝ) → ℝ := enumH (sInf {n | HSpec (enumH n)})
#check_explicit_rejects viaSInf

/-- ℚ-encoded certificates: the `n`-th certificate is `(n, 1/(n+1))`. -/
def cert (n : ℕ) : ℚ × ℚ := ((n : ℚ), 1 / ((n : ℚ) + 1))

/-- The certificate condition: explicit rational inequalities. -/
def CertOk (c : ℚ × ℚ) : Prop := c.2 < 1 / 10 ∧ 3 ≤ c.1

instance : DecidablePred CertOk := fun _ => inferInstanceAs (Decidable (_ ∧ _))

theorem exists_cert : ∃ n, CertOk (cert n) := ⟨10, by norm_num [CertOk, cert]⟩

/-- (b) `Nat.find` over ℚ-encoded certificates with a decidable rational inequality: ACCEPTED. -/
def leastCert : ℕ := Nat.find exists_cert
noncomputable def usesCert (x : ℝ) : ℝ := (leastCert : ℝ) * x + Real.sqrt x
#check_explicit leastCert
#check_explicit usesCert

/-- (b') the same search through the wrapper with a genuine instance: ACCEPTED. -/
def leastCert' : ℕ := myFind (fun n => CertOk (cert n)) exists_cert
#check_explicit leastCert'

/-- (b'') definite description over `ℚ × ℚ` with a genuinely decidable predicate: ACCEPTED. -/
theorem existsUnique_cert : ∃! c : ℚ × ℚ, c = cert 10 ∧ CertOk c :=
  ⟨cert 10, ⟨rfl, by norm_num [CertOk, cert]⟩, fun _ h => h.1⟩
noncomputable def theCert : ℚ × ℚ := the existsUnique_cert
#check_explicit theCert

end ExplicitSearchTest

/-! ## Uniformity of oracle machines (`#check_constructive`)

A machine that branches on an undecidable property of the real number behind its oracle
is rejected, even though `#check_explicit` accepts classical decidability in formulas. -/
noncomputable def branchOnReal (x : ℝ) (q : ℕ → ℕ) : ℕ →. ℕ :=
  open Classical in if x < 1/3 then fun n => Part.some (q n) else fun _ => Part.some 0
#check_constructive_rejects branchOnReal
def plainMachine (q : ℕ → ℕ) : ℕ →. ℕ := fun n => Part.some (q (n + 1))
#check_constructive plainMachine
