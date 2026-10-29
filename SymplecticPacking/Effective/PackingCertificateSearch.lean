import SymplecticPacking.Effective.PackingCertificateSearchInput
import SymplecticPacking.Effective.PackingCertificateCompleteness

/-!
# The finite certificate search

The finite search: source enclosures and every source/grid-cell Euler table.
-/

namespace SymplecticPacking.Effective.PackingSearch
open RationalCode PackingCertificate PackingPolynomial PackingPolynomialCode
open PackingCertificateCode PackingSearchInput
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Precision, clipping box, source box, grid level, Euler mesh and polynomial program. -/
abbrev Candidate := ℕ × (ℕ × (ℕ × (ℕ × (ℕ × List ℕ))))

def encodeCandidate (a : Candidate) : ℕ := Nat.pair a.1 (Nat.pair a.2.1
  (Nat.pair a.2.2.1 (Nat.pair a.2.2.2.1 (Nat.pair a.2.2.2.2.1
    (Encodable.encode a.2.2.2.2.2)))))

def decodeCandidate (s : ℕ) : Candidate :=
  let s₁:=Nat.unpair s
  let s₂:=Nat.unpair s₁.2
  let s₃:=Nat.unpair s₂.2
  let s₄:=Nat.unpair s₃.2
  let s₅:=Nat.unpair s₄.2
  (s₁.1,(s₂.1,(s₃.1,(s₄.1,(s₅.1,PackingStateList.decodeList s₅.2)))))

@[simp] theorem decode_encodeCandidate (a : Candidate) : decodeCandidate (encodeCandidate a)=a := by
  rcases a with ⟨p,B,Q,m,N,program⟩
  simp [encodeCandidate,decodeCandidate,PackingStateList.decodeList]

def rhoCode (Q m : ℕ) : ℕ := mulCode (dimCode (2*Q)) (dyadicCode m)

@[simp] theorem rhoCode_value (Q m : ℕ) : value (rhoCode Q m)=boxRadius Q m := by
  simp [rhoCode,boxRadius,value_mulCode,value_dyadicCode]

/-- `x=pair (pair n stage) sourceIndex`. -/
def enclosureTerm (centres radii : ℕ → ℕ) (x : ℕ) : ℕ :=
  let n:=(Nat.unpair (Nat.unpair x).1).1
  let a:=decodeCandidate (Nat.unpair (Nat.unpair x).1).2
  let i:=(Nat.unpair x).2
  coordinateFailure (2*n) (sourceState centres (2*n) i a.1)
    (outerRadiusCode (2*n) (fun p=>radii (Nat.pair i p)) a.1) (dimCode a.2.2.1)

/-- `x=pair (pair (pair n stage) sourceIndex) gridIndex`. -/
def cellTerm (centres radii target : ℕ → ℕ) (x : ℕ) : ℕ :=
  let n:=(Nat.unpair (Nat.unpair (Nat.unpair x).1).1).1
  let a:=decodeCandidate (Nat.unpair (Nat.unpair (Nat.unpair x).1).1).2
  let i:=(Nat.unpair (Nat.unpair x).1).2
  let g:=(Nat.unpair x).2
  let ρ:=rhoCode a.2.2.1 a.2.2.2.1
  let H:=programBudget a.2.1 a.2.2.2.2.2
  cellFailure (2*n) (universalField n) a.2.2.2.2.1
    (candidateCode a.2.1 a.2.2.2.2.2)
    (boxNodeCode (2*n) a.2.2.1 a.2.2.2.1 g)
    (sourceState centres (2*n) i a.1) ρ
    (outerRadiusCode (2*n) (fun p=>radii (Nat.pair i p)) a.1)
    (errorCode H a.2.2.2.2.1 ρ) (plateauCode a.2.1) (innerRadiusCode target a.1)

/-- A source is checked against every cell of the finite source box. -/
def sourceCells (centres radii target : ℕ → ℕ) (x : ℕ) : ℕ :=
  let n:=(Nat.unpair (Nat.unpair x).1).1
  let a:=decodeCandidate (Nat.unpair (Nat.unpair x).1).2
  sumFailure (cellTerm centres radii target) x (FiniteGrid.count (2*n) a.2.2.2.1)

/-- All loops have finite natural-number bounds. Zero means acceptance. -/
def stageFailure (centres radii target : ℕ → ℕ) (n k s : ℕ) : ℕ :=
  let a:=decodeCandidate s
  (if 0<a.2.1 ∧ 0<a.2.2.1 ∧ 0<a.2.2.2.2.1 then 0 else 1) +
    sumFailure (enclosureTerm centres radii) (Nat.pair n s) k +
    sumFailure (sourceCells centres radii target) (Nat.pair n s) k

theorem stageFailure_zero (centres radii target : ℕ → ℕ) (n k s : ℕ) :
    stageFailure centres radii target n k s=0 ↔
    (let a:=decodeCandidate s
     1≤a.2.1 ∧ 0<a.2.2.1 ∧ 0<a.2.2.2.2.1 ∧
       (∀ i<k,enclosureTerm centres radii (Nat.pair (Nat.pair n s) i)=0) ∧
       ∀ i<k,∀ g<FiniteGrid.count (2*n) a.2.2.2.1,
         cellTerm centres radii target (Nat.pair (Nat.pair (Nat.pair n s) i) g)=0) := by
  dsimp only
  constructor
  · intro h
    dsimp only [stageFailure] at h
    have hparts:=Nat.add_eq_zero_iff.mp h
    have hfirst:=Nat.add_eq_zero_iff.mp hparts.1
    have hg : 0<(decodeCandidate s).2.1 ∧ 0<(decodeCandidate s).2.2.1 ∧
        0<(decodeCandidate s).2.2.2.2.1 := by
      by_contra hn
      have hh : (1:ℕ)=0 := by simpa only [if_neg hn] using hfirst.1
      omega
    refine ⟨by omega,hg.2.1,hg.2.2,(sumFailure_zero _ _ _).mp hfirst.2,?_⟩
    intro i hi
    have hh:=(sumFailure_zero _ _ _).mp hparts.2 i hi
    simpa only [sourceCells,Nat.unpair_pair,sumFailure_zero] using hh
  · rintro ⟨hB,hQ,hN,he,hc⟩
    dsimp only [stageFailure]
    have hg : 0<(decodeCandidate s).2.1 ∧ 0<(decodeCandidate s).2.2.1 ∧
        0<(decodeCandidate s).2.2.2.2.1 := ⟨by omega,hQ,hN⟩
    rw [if_pos hg,(sumFailure_zero _ _ _).mpr he]
    have hh : sumFailure (sourceCells centres radii target) (Nat.pair n s) k=0 := by
      apply (sumFailure_zero _ _ _).mpr
      intro i hi
      simpa only [sourceCells,Nat.unpair_pair,sumFailure_zero] using hc i hi
    rw [hh]

/-- No extra certificate oracle appears in this completeness statement. -/
theorem exists_stage {n k : ℕ} {C₀ Cmid C : ℝ} {c : Fin k → ℝ} {s : Fin k → Problem.E n}
    {H : ℝ → Problem.E n → ℝ} (centres radii target : ℕ → ℕ)
    (hpack : Problem.PackingSpec n k C₀ c s H) (hC₀ : 0<C₀)
    (hmid : C₀<Cmid) (hC : Cmid<C) (hc : ∀ i,0<c i)
    (hs : ∀ i : Fin k,∀ j : Fin (2*n),Names
      (fun p=>value (centres (Nat.pair (Nat.pair i.val p) j.val))) (s i j))
    (hr : ∀ i : Fin k,Names (fun p=>value (radii (Nat.pair i.val p))) (Real.sqrt (c i/Real.pi)))
    (ht : Names (fun p=>value (target p)) (Real.sqrt (C/Real.pi))) :
    ∃ st,stageFailure centres radii target n k st=0 := by
  obtain ⟨p,B,Q,m,N,program,hB,hQ,hN,hencl,hcell⟩ :=
    exists_finite_checks hpack hC₀ hmid hC hc hs hr ht
  let a : Candidate := (p,(B,(Q,(m,(N,program)))))
  refine ⟨encodeCandidate a,(stageFailure_zero _ _ _ _ _ _).mpr ?_⟩
  simp only [decode_encodeCandidate]
  refine ⟨hB,hQ,hN,?_,?_⟩
  · intro i hi
    dsimp only [enclosureTerm]
    simp only [Nat.unpair_pair,decode_encodeCandidate]
    rw [coordinateFailure_zero,sourceState_decode]
    intro j
    have hh:=hencl ⟨i,hi⟩ j
    have heq : value (outerRadiusCode (2*n) (fun p=>radii (Nat.pair i p)) p)=
        outerRadius (2*n) (fun p=>value (radii (Nat.pair i p))) p := outerRadiusCode_value _ _ _
    rw [dimCode_value,heq]
    exact_mod_cast hh
  · intro i hi g hg
    dsimp only [cellTerm]
    simp only [Nat.unpair_pair,decode_encodeCandidate]
    rw [cellFailure_zero,sourceState_decode,rhoCode_value,outerRadiusCode_value,
      errorCode_value _ _ _ hN,rhoCode_value,plateauCode_value,innerRadiusCode_value,
      programBudget_correct]
    exact hcell ⟨i,hi⟩ g hg

/-- The output is selected only by finite natural arithmetic. -/
noncomputable def stageOutput (n st : ℕ) :=
  let a:=decodeCandidate st
  output n a.2.1 (programExpression a.2.2.2.2.2)

/-- Passing all finite loops certifies the entire closed source balls. -/
theorem stage_sound {n k : ℕ} {C : ℝ} {c : Fin k → ℝ} {s : Fin k → Problem.E n}
    (centres radii target : ℕ → ℕ) {st : ℕ}
    (hpass : stageFailure centres radii target n k st=0) (hC : 0<C)
    (hc : ∀ i,0<c i)
    (hs : ∀ i : Fin k,∀ j : Fin (2*n),Names
      (fun p=>value (centres (Nat.pair (Nat.pair i.val p) j.val))) (s i j))
    (hr : ∀ i : Fin k,Names (fun p=>value (radii (Nat.pair i.val p))) (Real.sqrt (c i/Real.pi)))
    (ht : Names (fun p=>value (target p)) (Real.sqrt (C/Real.pi))) :
    Problem.PackingSpec n k C c s (stageOutput n st).hamiltonian := by
  rcases ha : decodeCandidate st with ⟨p,B,Q,m,N,program⟩
  have hz := (stageFailure_zero centres radii target n k st).mp hpass
  rw [ha] at hz
  rcases hz with ⟨hB,hQ,hN,hencl,hchecks⟩
  let src : Fin k → ℕ := fun i=>sourceState centres (2*n) i.val p
  let rad : Fin k → ℕ := fun i=>outerRadiusCode (2*n) (fun p=>radii (Nat.pair i.val p)) p
  have hsrc (i : Fin k) : ODECode.rationalState (ODECode.decodeState (2*n) (src i))=
      fun j=>value (centres (Nat.pair (Nat.pair i.val p) j.val)) := by
    dsimp only [src]
    rw [sourceState_decode]
    rfl
  have hrad (i : Fin k) : value (rad i)=
      outerRadius (2*n) (fun p=>value (radii (Nat.pair i.val p))) p :=
    outerRadiusCode_value _ _ _
  have hsource : ∀ i,∀ x∈Problem.capBall (s i) (c i),
      ‖l2Vector ((fun j=>x j)-ODECode.realState (ODECode.decodeState (2*n) (src i)))‖≤
        (value (rad i):ℝ) := by
    intro i x hx
    have hxrad : ‖l2Vector ((fun j=>x j)-(fun j=>s i j))‖≤Real.sqrt (c i/Real.pi) := by
      rw [l2Vector_sub]
      change ‖x-s i‖≤Real.sqrt (c i/Real.pi)
      apply Real.le_sqrt_of_sq_le
      apply (le_div_iff₀ Real.pi_pos).mpr
      change Real.pi*‖x-s i‖^2≤c i at hx
      simpa only [mul_comm] using hx
    have hh := outerBall_contains (hs i) (hr i) p hxrad
    rw [hrad]
    apply le_of_lt
    convert hh using 1
    congr 2
    funext j
    change x j-(value (ODECode.decodeState (2*n) (src i) j):ℝ)=_
    rw [show ODECode.decodeState (2*n) (src i)=
      (fun j=>centres (Nat.pair (Nat.pair i.val p) j.val)) from sourceState_decode _ _ _ _]
    rfl
  have hencl' : ∀ i : Fin k,∀ j : Fin (2*n),
      |ODECode.rationalState (ODECode.decodeState (2*n) (src i)) j|+value (rad i)<(Q:ℚ) := by
    intro i j
    have hh:=hencl i.val i.isLt
    dsimp only [enclosureTerm] at hh
    simp only [Nat.unpair_pair,ha] at hh
    simpa only [dimCode_value,src,rad] using (coordinateFailure_zero _ _ _ _).mp hh j
  have hcover : ∀ i,∀ x∈Problem.capBall (s i) (c i),
      ∃ a : Fin (FiniteGrid.count (2*n) m),
      ‖ODECode.realState (ODECode.decodeState (2*n) (boxNodeCode (2*n) Q m a.val))-
        (fun j=>x j)‖≤(value (rhoCode Q m):ℝ) := by
    intro i x hx
    have hbox : ∀ j, |x j|≤(Q:ℝ) := by
      intro j
      have hrj := PiLp.norm_apply_le
        (l2Vector ((fun j=>x j)-ODECode.realState (ODECode.decodeState (2*n) (src i)))) j
      have he : |(value (ODECode.decodeState (2*n) (src i) j):ℝ)|+
          (value (rad i):ℝ)<(Q:ℝ) := by exact_mod_cast hencl' i j
      have hh:=hsource i x hx
      have htri := abs_add_le (x j-ODECode.realState (ODECode.decodeState (2*n) (src i)) j)
        (ODECode.realState (ODECode.decodeState (2*n) (src i)) j)
      simp only [Pi.sub_apply,l2Vector_apply,Real.norm_eq_abs,ODECode.realState] at hrj
      simp only [sub_add_cancel,ODECode.realState] at htri
      linarith
    obtain ⟨g,hg,hh⟩:=box_covered (2*n) Q m hQ (fun j=>x j) hbox
    refine ⟨⟨g,hg⟩,?_⟩
    have hnode : ODECode.realState (ODECode.decodeState (2*n) (boxNodeCode (2*n) Q m g))=
        ODE.castVector (boxNode (2*n) Q m g) := by
      rw [boxNodeCode,ODECode.decodeState_encodeState]
      change ODE.castVector (ODECode.rationalState (boxNodeState (2*n) Q m g))=_
      rw [boxNodeState_value]
    rw [hnode,rhoCode_value,norm_sub_rev]
    exact hh
  have hradpos : ∀ i,0≤value (rad i) := by
    intro i
    have hh := (outerRadius_bounds (hr i) (2*n) p).1
    rw [hrad]
    have hp : (0:ℝ)≤radius p := by exact_mod_cast (radius_pos p).le
    have hr0 := Real.sqrt_nonneg (c i/Real.pi)
    have hz : (0:ℝ)≤outerRadius (2*n) (fun p=>value (radii (Nat.pair i.val p))) p := (add_nonneg hr0 (mul_nonneg (Nat.cast_nonneg _) hp)).trans hh
    exact_mod_cast hz
  have hcheck : ∀ i : Fin k,∀ a : Fin (FiniteGrid.count (2*n) m),
      cellFailure (2*n) (universalField n) N (candidateCode B program)
      (boxNodeCode (2*n) Q m a.val) (src i) (rhoCode Q m) (rad i)
      (errorCode (programBudget B program) N (rhoCode Q m)) (plateauCode B)
      (innerRadiusCode target p)=0 := by
    intro i a
    have hh:=hchecks i.val i.isLt a.val a.isLt
    simpa only [cellTerm,Nat.unpair_pair,ha,src,rad] using hh
  have hout := finite_cover_sound program
    (fun a : Fin (FiniteGrid.count (2*n) m)=>boxNodeCode (2*n) Q m a.val) src rad
    hB hN hC
    (by rw [rhoCode_value,boxRadius]; exact mul_nonneg (by positivity) (radius_pos m).le) hradpos
    (by rw [errorCode_value _ _ _ hN,programBudget_correct])
    (plateauCode_value B) (by
      rw [innerRadiusCode_value]
      exact (innerRadius_bounds ht (Real.sqrt_nonneg _) p).2)
    hcover hsource hcheck
  simpa only [stageOutput,ha] using hout

#check_explicit stageFailure
end SymplecticPacking.Effective.PackingSearch
