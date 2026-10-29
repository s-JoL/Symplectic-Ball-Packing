import SymplecticPacking.HighDim.Handle.RawRationalBoxBasis
import SymplecticPacking.HighDim.Handle.QuadricFiniteOverlap
import SymplecticPacking.HighDim.Handle.QuadricTightFiniteNerve

/-!
# A finite overlap tree for the quadric atlas

A deterministic earlier-parent tree from a supplied finite list and Boolean edges.
-/

namespace SymplecticPacking.HighDim.ToricPackingStages.FiniteOverlapTree
open Set Function
variable {I : Type} [DecidableEq I]

def candidate (edge : I → I → Bool) (seen : List I) (v : I) : Bool :=
  decide (v ∉ seen) && seen.any (fun p => edge v p)

def next (vertices : List I) (edge : I → I → Bool) (seen : List I) : Option I :=
  vertices.find? (candidate edge seen)

def grow (vertices : List I) (edge : I → I → Bool) (seen : List I) : List I :=
  match next vertices edge seen with
  | none => seen
  | some v => seen ++ [v]

def visits (vertices : List I) (edge : I → I → Bool) (root : I) : ℕ → List I
  | 0 => [root]
  | n+1 => grow vertices edge (visits vertices edge root n)

def order (vertices : List I) (edge : I → I → Bool) (root : I) : List I :=
  visits vertices edge root vertices.length

lemma next_some {vertices seen : List I} {edge : I → I → Bool} {v : I}
    (h : next vertices edge seen = some v) :
    v ∈ vertices ∧ v ∉ seen ∧ ∃ p ∈ seen, edge v p = true := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  exact ⟨hm, by simpa only [candidate, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] using hp⟩

lemma mem_grow {vertices seen : List I} {edge : I → I → Bool} {v : I}
    (hv : v ∈ seen) : v ∈ grow vertices edge seen := by
  unfold grow
  cases next vertices edge seen <;> simp [hv]

lemma grow_inside {vertices seen : List I} {edge : I → I → Bool}
    (h : ∀ v ∈ seen, v ∈ vertices) : ∀ v ∈ grow vertices edge seen, v ∈ vertices := by
  intro v hv
  unfold grow at hv
  split at hv
  · exact h v hv
  · rename_i w hw
    rcases List.mem_append.mp hv with hv | hv
    · exact h v hv
    · have hvw : v = w := by simpa using hv
      subst v
      exact (next_some hw).1

inductive Rooted (edge : I → I → Bool) (root : I) : List I → Prop
  | start : Rooted edge root [root]
  | append {seen : List I} {v : I} : Rooted edge root seen → v ∉ seen →
      (∃ p ∈ seen, edge v p = true) → Rooted edge root (seen ++ [v])

lemma rooted_nodup {edge : I → I → Bool} {root : I} {seen : List I}
    (h : Rooted edge root seen) : seen.Nodup := by
  induction h with
  | start => simp
  | @append seen v h hn hp ih =>
      apply List.nodup_append.mpr
      refine ⟨ih, by simp, ?_⟩
      intro a ha b hb
      have hb' : b = v := by simpa using hb
      subst b
      exact fun hav => hn (hav ▸ ha)

lemma rooted_first {edge : I → I → Bool} {root : I} {seen : List I}
    (h : Rooted edge root seen) : seen[0]?=some root := by
  induction h with
  | start => rfl
  | @append old v h hn hp ih =>
      cases old with
      | nil => simp at ih
      | cons w ws => simpa using ih

lemma rooted_grow {vertices seen : List I} {edge : I → I → Bool} {root : I}
    (h : Rooted edge root seen) : Rooted edge root (grow vertices edge seen) := by
  unfold grow
  split
  · exact h
  · rename_i v hv
    exact Rooted.append h (next_some hv).2.1 (next_some hv).2.2

lemma rooted_visits (vertices : List I) (edge : I → I → Bool) (root : I) (n : ℕ) :
    Rooted edge root (visits vertices edge root n) := by
  induction n with
  | zero => exact Rooted.start
  | succ n ih => exact rooted_grow ih

lemma root_mem_visits (vertices : List I) (edge : I → I → Bool) (root : I) (n : ℕ) :
    root ∈ visits vertices edge root n := by
  induction n with
  | zero => simp [visits]
  | succ n ih => exact mem_grow ih

lemma visits_inside {vertices : List I} {edge : I → I → Bool} {root : I}
    (hr : root ∈ vertices) (n : ℕ) : ∀ v ∈ visits vertices edge root n, v ∈ vertices := by
  induction n with
  | zero => simpa only [visits, List.mem_singleton, forall_eq] using hr
  | succ n ih => exact grow_inside ih

lemma path_crossing {edge : I → I → Bool} {root v : I} {seen : List I}
    (hpath : Relation.TransGen (fun a b => edge b a = true) root v)
    (hr : root ∈ seen) (hv : v ∉ seen) :
    ∃ w, w ∉ seen ∧ ∃ p ∈ seen, edge w p = true := by
  revert hv
  induction hpath with
  | single h => exact fun hv => ⟨_,hv,_,hr,h⟩
  | @tail b c hpath hbc ih =>
      intro hc
      by_cases hb : b ∈ seen
      · exact ⟨c,hc,b,hb,hbc⟩
      · exact ih hb

lemma next_ne_none {vertices seen : List I} {edge : I → I → Bool} {root v : I}
    (hall : ∀ i, i ∈ vertices)
    (hpath : ∀ i, Relation.TransGen (fun a b => edge b a = true) root i)
    (hr : root ∈ seen) (hv : v ∉ seen) : next vertices edge seen ≠ none := by
  intro hn
  obtain ⟨w, hw, p, hp, he⟩ := path_crossing (hpath v) hr hv
  have hc : candidate edge seen w = true := by
    simp only [candidate, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
    exact ⟨hw,p,hp,he⟩
  exact (List.find?_eq_none.mp hn w (hall w)) hc

lemma grow_length_of_missing {vertices seen : List I} {edge : I → I → Bool} {root v : I}
    (hall : ∀ i, i ∈ vertices)
    (hpath : ∀ i, Relation.TransGen (fun a b => edge b a = true) root i)
    (hr : root ∈ seen) (hv : v ∉ seen) :
    (grow vertices edge seen).length = seen.length+1 := by
  have hn := next_ne_none hall hpath hr hv
  unfold grow
  split
  · contradiction
  · simp

lemma length_lower_of_missing {vertices : List I} {edge : I → I → Bool} {root v : I}
    (hall : ∀ i, i ∈ vertices)
    (hpath : ∀ i, Relation.TransGen (fun a b => edge b a = true) root i)
    (n : ℕ) (hv : v ∉ visits vertices edge root n) :
    n+1 ≤ (visits vertices edge root n).length := by
  induction n with
  | zero => simp [visits]
  | succ n ih =>
      have hvn : v ∉ visits vertices edge root n := fun h => hv (mem_grow h)
      have hg := grow_length_of_missing hall hpath (root_mem_visits vertices edge root n) hvn
      change n+1+1 ≤ (grow vertices edge (visits vertices edge root n)).length
      rw [hg]
      exact Nat.succ_le_succ (ih hvn)

/-- The finite expansion terminates after at most the supplied list length. -/
theorem order_covers {vertices : List I} {edge : I → I → Bool} {root : I}
    (hall : ∀ i, i ∈ vertices)
    (hpath : ∀ i, Relation.TransGen (fun a b => edge b a = true) root i) :
    ∀ v, v ∈ order vertices edge root := by
  intro v
  by_contra hv
  have hlow := length_lower_of_missing hall hpath vertices.length hv
  have hn := rooted_nodup (rooted_visits vertices edge root vertices.length)
  have hsub : (visits vertices edge root vertices.length).toFinset ⊆ vertices.toFinset := by
    intro x hx
    exact List.mem_toFinset.mpr (visits_inside (hall root) _ _ (List.mem_toFinset.mp hx))
  have hhigh := (Finset.card_le_card hsub).trans vertices.toFinset_card_le
  rw [List.toFinset_card_of_nodup hn] at hhigh
  omega

/-- Every noninitial vertex has a genuine edge to an earlier vertex. -/
theorem rooted_earlier {edge : I → I → Bool} {root : I} {seen : List I}
    (h : Rooted edge root seen) (i : ℕ) (hi : i < seen.length) (hzero : 0 < i) :
    ∃ k, ∃ hk : k < i, edge seen[i] seen[k] = true := by
  induction h with
  | start => simp at hi; omega
  | @append old v h hn hp ih =>
      by_cases hio : i < old.length
      · obtain ⟨k,hk,he⟩ := ih hio
        refine ⟨k,hk,?_⟩
        simpa only [List.getElem_append_left hio, List.getElem_append_left (hk.trans hio)] using he
      · have hie : i = old.length := by simp only [List.length_append, List.length_singleton] at hi; omega
        subst i
        obtain ⟨p,hp,he⟩ := hp
        obtain ⟨k,hk,hkp⟩ := List.mem_iff_getElem.mp hp
        refine ⟨k,hk,?_⟩
        simpa [List.getElem_append, hk, hkp] using he

/-- The parent is the first earlier vertex satisfying the Boolean edge test. -/
def parentIndex (edge : I → I → Bool) (root : I) (seen : List I) (i : ℕ) : ℕ :=
  (seen.take i).findIdx (fun p => edge (seen[i]?.getD root) p)

lemma parentIndex_lt {edge : I → I → Bool} {root : I} {seen : List I}
    (h : Rooted edge root seen) (i : ℕ) (hi : i < seen.length) (hzero : 0 < i) :
    parentIndex edge root seen i < i := by
  obtain ⟨k,hk,he⟩ := rooted_earlier h i hi hzero
  have hkt : k < (seen.take i).length := by simp only [List.length_take]; omega
  have hex : ∃ p ∈ seen.take i, edge (seen[i]?.getD root) p = true := by
    refine ⟨(seen.take i)[k], List.getElem_mem _, ?_⟩
    simpa only [List.getElem_take, List.getElem?_eq_getElem hi, Option.getD_some] using he
  have hp := List.findIdx_lt_length_of_exists hex
  exact hp.trans_le (by simp only [List.length_take]; exact min_le_left _ _)

lemma parentIndex_edge {edge : I → I → Bool} {root : I} {seen : List I}
    (h : Rooted edge root seen) (i : ℕ) (hi : i < seen.length) (hzero : 0 < i) :
    edge seen[i] (seen[parentIndex edge root seen i]'( (parentIndex_lt h i hi hzero).trans hi )) = true := by
  have hp := parentIndex_lt h i hi hzero
  have hpt : parentIndex edge root seen i < (seen.take i).length := by
    simp only [List.length_take]
    omega
  have he := List.findIdx_getElem (p := fun p => edge (seen[i]?.getD root) p)
    (xs := seen.take i) (w := hpt)
  simpa only [parentIndex, List.getElem_take, List.getElem?_eq_getElem hi, Option.getD_some] using he

def parent {edge : I → I → Bool} {root : I} {seen : List I}
    (h : Rooted edge root seen) (i : Fin (seen.length-1)) : Fin (i.val+1) :=
  ⟨parentIndex edge root seen (i.val+1), parentIndex_lt h _ (by omega) (by omega)⟩

/-- Only the first `n` finite stages of a scalar checker are considered. -/
def prefixEdge (check : I → I → ℕ → ℕ) (n : ℕ) (i j : I) : Bool :=
  (List.range n).any (fun s => decide (check i j s=0))

lemma prefixEdge_iff (check : I → I → ℕ → ℕ) (n : ℕ) (i j : I) :
    prefixEdge check n i j=true ↔ ∃ s<n, check i j s=0 := by
  simp [prefixEdge, List.any_eq_true]

lemma prefixEdge_mono {check : I → I → ℕ → ℕ} {n N : ℕ} (hn : n ≤ N)
    {i j : I} (h : prefixEdge check n i j=true) : prefixEdge check N i j=true := by
  obtain ⟨s,hs,he⟩ := (prefixEdge_iff _ _ _ _).mp h
  exact (prefixEdge_iff _ _ _ _).mpr ⟨s,hs.trans_le hn,he⟩

lemma prefixPath_mono {check : I → I → ℕ → ℕ} {n N : ℕ} (hn : n ≤ N) {i j : I}
    (h : Relation.TransGen (fun a b => prefixEdge check n b a=true) i j) :
    Relation.TransGen (fun a b => prefixEdge check N b a=true) i j :=
  by
    induction h with
    | single he => exact .single (prefixEdge_mono hn he)
    | tail _ he ih => exact ih.tail (prefixEdge_mono hn he)

/-- A finite geometric path uses only finitely many successful scalar-check stages. -/
lemma path_has_prefix {R : I → I → Prop} {check : I → I → ℕ → ℕ}
    (hc : ∀ i j, R i j → ∃ s,check j i s=0) {i j : I}
    (h : Relation.TransGen R i j) :
    ∃ n, Relation.TransGen (fun a b => prefixEdge check n b a=true) i j := by
  induction h with
  | @single j hij =>
      obtain ⟨s,hs⟩ := hc _ j hij
      exact ⟨s+1,.single ((prefixEdge_iff _ _ _ _).mpr ⟨s,by omega,hs⟩)⟩
  | @tail j k hij hjk ih =>
      obtain ⟨n,hn⟩ := ih
      obtain ⟨s,hs⟩ := hc j k hjk
      refine ⟨max n (s+1), (prefixPath_mono (le_max_left _ _) hn).tail ?_⟩
      exact (prefixEdge_iff _ _ _ _).mpr ⟨s,by omega,hs⟩

/-- A Boolean test on the supplied finite vertex list. -/
def prefixConnected (vertices : List I) (check : I → I → ℕ → ℕ) (root : I) (n : ℕ) : Bool :=
  vertices.all (fun v => decide (v ∈ order vertices (prefixEdge check n) root))

lemma prefixConnected_iff (vertices : List I) (check : I → I → ℕ → ℕ) (root : I) (n : ℕ) :
    prefixConnected vertices check root n=true ↔
      ∀ v∈vertices,v ∈ order vertices (prefixEdge check n) root := by
  simp [prefixConnected, List.all_eq_true]

lemma exists_connected_prefix (vertices : List I) (check : I → I → ℕ → ℕ) (root : I)
    (hall : ∀ i,i∈vertices)
    (hpath : ∀ v,∃ n,Relation.TransGen (fun a b => prefixEdge check n b a=true) root v) :
    ∃ n,prefixConnected vertices check root n=true := by
  have hfinite (vs : List I) : ∃ n,∀ v∈vs,
      Relation.TransGen (fun a b => prefixEdge check n b a=true) root v := by
    induction vs with
    | nil => exact ⟨0,by simp⟩
    | cons v vs ih =>
        obtain ⟨n,hn⟩ := hpath v
        obtain ⟨N,hN⟩ := ih
        refine ⟨max n N,?_⟩
        intro w hw
        rcases List.mem_cons.mp hw with rfl | hw
        · exact prefixPath_mono (le_max_left _ _) hn
        · exact prefixPath_mono (le_max_right _ _) (hN w hw)
  obtain ⟨n,hn⟩ := hfinite vertices
  refine ⟨n,(prefixConnected_iff _ _ _ _).mpr ?_⟩
  exact fun v _ => order_covers hall (fun w => hn w (hall w)) v

/-- Least successful finite graph prefix. The decision procedure is the displayed
Boolean computation on finite lists and scalar certificates. -/
def connectedPrefix (vertices : List I) (check : I → I → ℕ → ℕ) (root : I)
    (hex : ∃ n,prefixConnected vertices check root n=true) : ℕ := Nat.find hex

lemma connectedPrefix_spec (vertices : List I) (check : I → I → ℕ → ℕ) (root : I)
    (hex : ∃ n,prefixConnected vertices check root n=true) :
    ∀ v∈vertices,v∈order vertices (prefixEdge check (connectedPrefix vertices check root hex)) root :=
  (prefixConnected_iff _ _ _ _).mp (Nat.find_spec hex)

/-- A bounded list search decodes a successful edge certificate. -/
def edgeWitness (check : I → I → ℕ → ℕ) (n : ℕ) (i j : I) : ℕ :=
  ((List.range n).find? (fun s => decide (check i j s=0))).getD 0

lemma edgeWitness_spec {check : I → I → ℕ → ℕ} {n : ℕ} {i j : I}
    (h : prefixEdge check n i j=true) : check i j (edgeWitness check n i j)=0 := by
  obtain ⟨s,hs,he⟩ := (prefixEdge_iff _ _ _ _).mp h
  have hn : (List.range n).find? (fun t => decide (check i j t=0)) ≠ none := by
    intro hh
    exact (List.find?_eq_none.mp hh s (List.mem_range.mpr hs)) (by simpa only [decide_eq_true_eq] using he)
  unfold edgeWitness
  cases hh : (List.range n).find? (fun t => decide (check i j t=0)) with
  | none => exact (hn hh).elim
  | some t => simpa only [Option.getD_some, decide_eq_true_eq] using List.find?_some hh

#check_explicit prefixConnected
#check_explicit connectedPrefix
#check_explicit edgeWitness

#check_explicit order
#check_explicit parentIndex
#check_explicit parent

end SymplecticPacking.HighDim.ToricPackingStages.FiniteOverlapTree

noncomputable section
namespace SymplecticPacking.HighDim.ToricPackingStages
open Set Function
open OAI.PackingSufficiencySupport.DiagonalQuadrics
open FiniteOverlapTree

private lemma innerOpen_subset_carrier {M : Type} [TopologicalSpace M]
    (B : RawCoordinateBox M) : B.innerOpen ⊆ B.carrier := by
  intro x hx
  refine ⟨hx.1,Metric.ball_subset_ball ?_ hx.2⟩
  linarith [B.radius_pos]

variable {m : ℕ} (a : Fin m → ℚ)
  [Fact (Injective (fun j => (a j:ℂ)))] [Fact (∀ j, (a j:ℂ) ≠ 0)]

/-- Native finite equality, including the explicitly indexed Boolean sign vector. -/
instance quadricTightFiniteIndex_decidableEq (R : ℚ) : DecidableEq (QuadricTightFiniteIndex a R) := by
  unfold QuadricTightFiniteIndex QuadricTightOrdinaryIndex OrdinaryGridIndex
  letI : DecidableEq (Fin m → Bool) := Fintype.decidablePiFintype
  infer_instance

lemma exists_quadricTreePrefix {R : ℚ} (hR : 0 < R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (hbranch : ∀ i, ‖(a i:ℂ)‖ < (R:ℝ)^2) :
    ∃ n,prefixConnected (quadricTightVertices a R) (quadricOverlapCheck a hR.le)
      (quadricTightRoot a hR.le hsep₀) n=true := by
  apply exists_connected_prefix _ _ _ (mem_quadricTightVertices a R)
  intro v
  apply path_has_prefix (R := fun i j =>
    ((quadricTightFiniteBox a hR.le hsep₀ hsep i).innerOpen ∩
      (quadricTightFiniteBox a hR.le hsep₀ hsep j).innerOpen).Nonempty)
  · intro i j hij
    obtain ⟨x,hxi,hxj⟩ := hij
    exact exists_quadricOverlapCheck a hR.le hsep₀ hsep j i
      ⟨x,innerOpen_subset_carrier _ hxj,innerOpen_subset_carrier _ hxi⟩
  · exact quadricTightFiniteBox_nerve_connected a hR hsep₀ hsep hbranch _ v

/-- The least finite prefix whose certified edges connect the explicit vertex list. -/
def quadricTreePrefix {R : ℚ} (hR : 0 < R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (hbranch : ∀ i, ‖(a i:ℂ)‖ < (R:ℝ)^2) : ℕ :=
  connectedPrefix (quadricTightVertices a R) (quadricOverlapCheck a hR.le)
    (quadricTightRoot a hR.le hsep₀) (exists_quadricTreePrefix a hR hsep₀ hsep hbranch)

/-- The deterministic order of all tight algebraic coordinate boxes. -/
def quadricTreeOrder {R : ℚ} (hR : 0 < R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (hbranch : ∀ i, ‖(a i:ℂ)‖ < (R:ℝ)^2) : List (QuadricTightFiniteIndex a R) :=
  order (quadricTightVertices a R)
    (prefixEdge (quadricOverlapCheck a hR.le) (quadricTreePrefix a hR hsep₀ hsep hbranch))
    (quadricTightRoot a hR.le hsep₀)

lemma quadricTreeOrder_covers {R : ℚ} (hR : 0 < R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (hbranch : ∀ i, ‖(a i:ℂ)‖ < (R:ℝ)^2) (v : QuadricTightFiniteIndex a R) :
    v ∈ quadricTreeOrder a hR hsep₀ hsep hbranch :=
  connectedPrefix_spec _ _ _ (exists_quadricTreePrefix a hR hsep₀ hsep hbranch) v
    (mem_quadricTightVertices a R v)

lemma quadricTreeOrder_rooted {R : ℚ} (hR : 0 < R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (hbranch : ∀ i, ‖(a i:ℂ)‖ < (R:ℝ)^2) :
    Rooted (prefixEdge (quadricOverlapCheck a hR.le) (quadricTreePrefix a hR hsep₀ hsep hbranch))
      (quadricTightRoot a hR.le hsep₀) (quadricTreeOrder a hR hsep₀ hsep hbranch) :=
  rooted_visits _ _ _ _

lemma quadricTreeOrder_length_pos {R : ℚ} (hR : 0 < R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (hbranch : ∀ i, ‖(a i:ℂ)‖ < (R:ℝ)^2) :
    0 < (quadricTreeOrder a hR hsep₀ hsep hbranch).length :=
  List.length_pos_of_mem (quadricTreeOrder_covers a hR hsep₀ hsep hbranch
    (quadricTightRoot a hR.le hsep₀))

/-- Natural-index access, with an explicit root default. -/
def quadricTreeAt {R : ℚ} (hR : 0 < R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (hbranch : ∀ i, ‖(a i:ℂ)‖ < (R:ℝ)^2) (i : ℕ) : QuadricTightFiniteIndex a R :=
  ((quadricTreeOrder a hR hsep₀ hsep hbranch)[i]?).getD (quadricTightRoot a hR.le hsep₀)

lemma quadricTreeAt_zero {R : ℚ} (hR : 0 < R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (hbranch : ∀ i, ‖(a i:ℂ)‖ < (R:ℝ)^2) :
    quadricTreeAt a hR hsep₀ hsep hbranch 0=quadricTightRoot a hR.le hsep₀ := by
  unfold quadricTreeAt
  rw [rooted_first (quadricTreeOrder_rooted a hR hsep₀ hsep hbranch), Option.getD_some]

lemma quadricTightRoot_point {R : ℚ} (hR : 0 ≤ R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖) :
    (quadricTightFiniteBox a hR hsep₀ hsep (quadricTightRoot a hR hsep₀)).point=0 := by
  rw [quadricTightFiniteBox_point]
  simp [quadricTightRationalPoint, quadricTightRoot, quadricZeroGrid_point, rationalPlane]

lemma quadricTightRoot_radius {R : ℚ} (hR : 0 ≤ R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖) :
    (quadricTightFiniteBox a hR hsep₀ hsep (quadricTightRoot a hR hsep₀)).radius=quadricGridRadius R := by
  rw [quadricTightFiniteBox_radius]
  rfl

def quadricTreeParent {R : ℚ} (hR : 0 < R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (hbranch : ∀ i, ‖(a i:ℂ)‖ < (R:ℝ)^2)
    (i : Fin ((quadricTreeOrder a hR hsep₀ hsep hbranch).length-1)) : Fin (i.val+1) :=
  parent (quadricTreeOrder_rooted a hR hsep₀ hsep hbranch) i

lemma quadricTreeParent_edge {R : ℚ} (hR : 0 < R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (hbranch : ∀ i, ‖(a i:ℂ)‖ < (R:ℝ)^2)
    (i : Fin ((quadricTreeOrder a hR hsep₀ hsep hbranch).length-1)) :
    prefixEdge (quadricOverlapCheck a hR.le) (quadricTreePrefix a hR hsep₀ hsep hbranch)
      (quadricTreeAt a hR hsep₀ hsep hbranch (i.val+1))
      (quadricTreeAt a hR hsep₀ hsep hbranch (quadricTreeParent a hR hsep₀ hsep hbranch i).val)=true := by
  have hi : i.val+1 < (quadricTreeOrder a hR hsep₀ hsep hbranch).length := by omega
  have hp := parentIndex_lt (quadricTreeOrder_rooted a hR hsep₀ hsep hbranch) _ hi (by omega)
  simpa only [quadricTreeAt, quadricTreeParent, parent, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem (hp.trans hi), Option.getD_some] using
    parentIndex_edge (quadricTreeOrder_rooted a hR hsep₀ hsep hbranch) _ hi (by omega)

/-- Each earlier-parent edge carries its finite scalar overlap certificate. -/
def quadricTreeOverlap {R : ℚ} (hR : 0 < R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (hbranch : ∀ i, ‖(a i:ℂ)‖ < (R:ℝ)^2)
    (i : Fin ((quadricTreeOrder a hR hsep₀ hsep hbranch).length-1)) :
    RawCoordinateBox (locus (fun j => (a j:ℂ))) :=
  quadricCheckedOverlap a hR.le hsep₀ hsep
    (quadricTreeAt a hR hsep₀ hsep hbranch (i.val+1))
    (quadricTreeAt a hR hsep₀ hsep hbranch (quadricTreeParent a hR hsep₀ hsep hbranch i).val)
    (edgeWitness (quadricOverlapCheck a hR.le) (quadricTreePrefix a hR hsep₀ hsep hbranch)
      (quadricTreeAt a hR hsep₀ hsep hbranch (i.val+1))
      (quadricTreeAt a hR hsep₀ hsep hbranch (quadricTreeParent a hR hsep₀ hsep hbranch i).val))
    (edgeWitness_spec (quadricTreeParent_edge a hR hsep₀ hsep hbranch i))

lemma quadricTreeAt_surjective {R : ℚ} (hR : 0 < R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (hbranch : ∀ i, ‖(a i:ℂ)‖ < (R:ℝ)^2) (v : QuadricTightFiniteIndex a R) :
    ∃ i : Fin ((quadricTreeOrder a hR hsep₀ hsep hbranch).length-1+1),
      quadricTreeAt a hR hsep₀ hsep hbranch i.val=v := by
  have hlen := quadricTreeOrder_length_pos a hR hsep₀ hsep hbranch
  obtain ⟨i,hi,hv⟩ := List.mem_iff_getElem.mp (quadricTreeOrder_covers a hR hsep₀ hsep hbranch v)
  refine ⟨⟨i,by omega⟩,?_⟩
  simpa only [quadricTreeAt, List.getElem?_eq_getElem hi, Option.getD_some] using hv

lemma quadricTree_inner_cover {R : ℚ} (hR : 0 < R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (hbranch : ∀ i, ‖(a i:ℂ)‖ < (R:ℝ)^2)
    (x : locus (fun j => (a j:ℂ))) (hx : ‖x.val.1‖ ≤ R) :
    ∃ i : Fin ((quadricTreeOrder a hR hsep₀ hsep hbranch).length-1+1),
      x ∈ (quadricTightFiniteBox a hR.le hsep₀ hsep (quadricTreeAt a hR hsep₀ hsep hbranch i.val)).innerOpen := by
  obtain ⟨v,hv⟩ := quadricTightFiniteBox_cover a hR.le hsep₀ hsep x hx
  obtain ⟨i,hi⟩ := quadricTreeAt_surjective a hR hsep₀ hsep hbranch v
  exact ⟨i,hi ▸ hv⟩

lemma quadricTreeOverlap_chart {R : ℚ} (hR : 0 < R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (hbranch : ∀ i, ‖(a i:ℂ)‖ < (R:ℝ)^2)
    (i : Fin ((quadricTreeOrder a hR hsep₀ hsep hbranch).length-1)) :
    (quadricTreeOverlap a hR hsep₀ hsep hbranch i).chart=
      (quadricTightRootChart a hR.le (quadricTreeAt a hR hsep₀ hsep hbranch (i.val+1))).chart := by
  unfold quadricTreeOverlap
  exact quadricCheckedOverlap_chart _ _ _ _ _ _ _ _

lemma quadricTreeOverlap_subset {R : ℚ} (hR : 0 < R)
    (hsep₀ : ∀ i, 1 ≤ ‖(a i:ℂ)‖) (hsep : ∀ i j, j≠i → 1 ≤ ‖(a i:ℂ)-(a j:ℂ)‖)
    (hbranch : ∀ i, ‖(a i:ℂ)‖ < (R:ℝ)^2)
    (i : Fin ((quadricTreeOrder a hR hsep₀ hsep hbranch).length-1)) :
    (quadricTreeOverlap a hR hsep₀ hsep hbranch i).compactCarrier ⊆
      (quadricTightFiniteBox a hR.le hsep₀ hsep
        (quadricTreeAt a hR hsep₀ hsep hbranch (i.val+1))).carrier ∩
      (quadricTightFiniteBox a hR.le hsep₀ hsep
        (quadricTreeAt a hR hsep₀ hsep hbranch (quadricTreeParent a hR hsep₀ hsep hbranch i).val)).carrier := by
  unfold quadricTreeOverlap
  exact quadricCheckedOverlap_subset _ _ _ _ _ _ _ _

#check_explicit quadricTreePrefix
#check_explicit quadricTreeOrder
#check_explicit quadricTreeParent
#check_explicit quadricTreeOverlap

end SymplecticPacking.HighDim.ToricPackingStages
