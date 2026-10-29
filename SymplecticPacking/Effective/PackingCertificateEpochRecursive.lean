import SymplecticPacking.Effective.PackingCertificateSearchRecursive
import SymplecticPacking.Effective.PackingCertificateCodeJoint
import SymplecticPacking.Effective.PackingCertificateGridJoint

/-!
# The Epoch certificate search as one oracle machine

A target-radius family is queried at the runtime ball count.
-/

namespace SymplecticPacking.Effective.PackingSearch.EpochRuntime
open RationalCode PackingCertificateCode PackingSearchInput PackingCertificate PackingPolynomialCode
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] PackingCodeJoint.coordinateFailure
  PackingGridJoint.boxNodeCode
attribute [local irreducible] cellTerm enclosureTerm sourceCells stageFailure sourceState

private theorem applyEncoded {O : Set (ℕ →. ℕ)} {α : Type*}
    [Primcodable α] [Inhabited α] {f : α → ℕ} (hf : Primrec f) {a : ℕ → α}
    (ha : Oracle.Total O (fun n=>Encodable.encode (a n))) :
    Oracle.Total O (fun n=>f (a n)) := by
  have hd : Primrec (fun c : ℕ => (Encodable.decode (α:=α) c).getD default) :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const default)
  exact (Oracle.comp (Oracle.of_computable (hf.comp hd).to_comp) ha).of_eq
    (fun n=>by simp)

theorem primitive_decodeCandidate : Primrec decodeCandidate := by
  have h₁:=Primrec.unpair
  have h₂:=Primrec.unpair.comp (Primrec.snd.comp h₁)
  have h₃:=Primrec.unpair.comp (Primrec.snd.comp h₂)
  have h₄:=Primrec.unpair.comp (Primrec.snd.comp h₃)
  have h₅:=Primrec.unpair.comp (Primrec.snd.comp h₄)
  unfold decodeCandidate
  exact (Primrec.fst.comp h₁).pair ((Primrec.fst.comp h₂).pair
    ((Primrec.fst.comp h₃).pair ((Primrec.fst.comp h₄).pair
      ((Primrec.fst.comp h₅).pair (PackingStateList.primitive_decodeList.comp (Primrec.snd.comp h₅))))))

attribute [local irreducible] decodeCandidate

theorem primitive_rhoCode : Primrec₂ rhoCode := by
  unfold rhoCode
  exact primitive_mulCode.comp (primitive_dimCode.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst))
    (primitive_dyadicCode.comp Primrec.snd)

attribute [local irreducible] rhoCode

private def outerCode (d q p : ℕ) :=
  addCode q (mulCode (dimCode (d+2)) (dyadicCode p))
private def innerCode (q p : ℕ) := maxCode zeroCode (addCode q (negCode (dyadicCode p)))

private theorem primitive_outerCode : Primrec (fun a : ℕ × (ℕ × ℕ)=>outerCode a.1 a.2.1 a.2.2) := by
  exact primitive_addCode.comp (Primrec.fst.comp Primrec.snd)
    (primitive_mulCode.comp (primitive_dimCode.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 2)))
      (primitive_dyadicCode.comp (Primrec.snd.comp Primrec.snd)))

private theorem primitive_innerCode : Primrec₂ innerCode :=
  primitive_maxCode.comp (Primrec.const zeroCode) (primitive_addCode.comp Primrec.fst
    (primitive_negCode.comp (primitive_dyadicCode.comp Primrec.snd)))

private theorem primitive_candidateCode : Primrec₂ candidateCode :=
  Primrec₂.natPair.comp Primrec.fst (Primrec.encode.comp Primrec.snd)

attribute [local irreducible] outerCode innerCode candidateCode programBudget errorCode plateauCode dimCode

private theorem cell_comp {α : Type*} [Primcodable α]
    {n N candidate initial source ρ r e plateau target : α → ℕ}
    (hn : Primrec n) (hN : Primrec N) (hc : Primrec candidate) (hi : Primrec initial)
    (hs : Primrec source) (hρ : Primrec ρ) (hr : Primrec r) (he : Primrec e)
    (hp : Primrec plateau) (ht : Primrec target) :
    Primrec (fun a=>PackingCodeJoint.cellFailure (n a) (N a) (candidate a) (initial a)
      (source a) (ρ a) (r a) (e a) (plateau a) (target a)) := by
  have hargs : Primrec (fun a=>(n a,N a,candidate a,initial a,source a,ρ a,r a,e a,plateau a,target a)) :=
    hn.pair (hN.pair (hc.pair (hi.pair (hs.pair (hρ.pair (hr.pair (he.pair (hp.pair ht))))))))
  exact PackingCodeJoint.primitive_cellFailure.comp hargs

private theorem coordinate_comp {α : Type*} [Primcodable α]
    {d state e R : α → ℕ} (hd : Primrec d) (hs : Primrec state) (he : Primrec e) (hR : Primrec R) :
    Primrec (fun a=>PackingCodeJoint.coordinateFailure (d a) (state a) (e a) (R a)) :=
  PackingCodeJoint.primitive_coordinateFailure.comp (hd.pair (hs.pair (he.pair hR)))

private abbrev FormulaArgs := ℕ × (Candidate × (ℕ × (ℕ × (ℕ × ℕ))))

private def cellFormula (u : FormulaArgs) : ℕ :=
  let n:=u.1
  let a:=u.2.1
  let g:=u.2.2.1
  let source:=u.2.2.2.1
  let radius:=u.2.2.2.2.1
  let target:=u.2.2.2.2.2
  let ρ:=rhoCode a.2.2.1 a.2.2.2.1
  PackingCodeJoint.cellFailure n a.2.2.2.2.1
    (candidateCode a.2.1 a.2.2.2.2.2) (PackingGridJoint.boxNodeCode (2*n) a.2.2.1 a.2.2.2.1 g)
    source ρ (outerCode (2*n) radius a.1)
    (errorCode (programBudget a.2.1 a.2.2.2.2.2) a.2.2.2.2.1 ρ)
    (plateauCode a.2.1) (innerCode target a.1)

attribute [local irreducible] cellFormula

private theorem primitive_cellFormula : Primrec cellFormula := by
  have hn : Primrec (fun u : FormulaArgs=>u.1) := Primrec.fst
  have ha : Primrec (fun u : FormulaArgs=>u.2.1) := Primrec.fst.comp Primrec.snd
  have hp:=Primrec.fst.comp ha
  have hB:=Primrec.fst.comp (Primrec.snd.comp ha)
  have hQ:=Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hm:=Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ha)))
  have hN:=Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ha))))
  have hprogram:=Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ha))))
  have hrest : Primrec (fun u : FormulaArgs=>u.2.2) := Primrec.snd.comp Primrec.snd
  have hg:=Primrec.fst.comp hrest
  have hsource:=Primrec.fst.comp (Primrec.snd.comp hrest)
  have hradius:=Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hrest))
  have htarget:=Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hrest))
  have hd:=Primrec.nat_mul.comp (Primrec.const 2) hn
  have hρ:=primitive_rhoCode.comp hQ hm
  have hinit:=PackingGridJoint.primitive_boxNodeCode.comp (hd.pair (hQ.pair (hm.pair hg)))
  have hcand:=primitive_candidateCode.comp hB hprogram
  have hr:=primitive_outerCode.comp (hd.pair (hradius.pair hp))
  have hbudget:=primitive_programBudget.comp hB hprogram
  have he:=primitive_errorCode.comp (hbudget.pair (hN.pair hρ))
  have hplateau:=primitive_plateauCode.comp hB
  have ht:=primitive_innerCode.comp htarget hp
  unfold cellFormula
  exact cell_comp hn hN hcand hinit hsource hρ hr he hplateau ht

private abbrev EnclosureArgs := ℕ × (Candidate × (ℕ × ℕ))
private def enclosureFormula (u : EnclosureArgs) : ℕ :=
  PackingCodeJoint.coordinateFailure (2*u.1) u.2.2.1
    (outerCode (2*u.1) u.2.2.2 u.2.1.1) (dimCode u.2.1.2.2.1)

attribute [local irreducible] enclosureFormula

private theorem primitive_enclosureFormula : Primrec enclosureFormula := by
  have hn : Primrec (fun u : EnclosureArgs=>2*u.1) := Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst
  have ha : Primrec (fun u : EnclosureArgs=>u.2.1) := Primrec.fst.comp Primrec.snd
  have hp:=Primrec.fst.comp ha
  have hQ:=Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hs : Primrec (fun u : EnclosureArgs=>u.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hrad : Primrec (fun u : EnclosureArgs=>u.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hh := coordinate_comp hn hs (primitive_outerCode.comp (hn.pair (hrad.pair hp)))
    (primitive_dimCode.comp hQ)
  exact hh.of_eq (fun u=>by unfold enclosureFormula; rfl)

private theorem enclosureTerm_recursive {O : Set (ℕ →. ℕ)} {centres radii : ℕ → ℕ}
    (hc : Oracle.Total O centres) (hr : Oracle.Total O radii) :
    Oracle.Total O (enclosureTerm centres radii) := by
  have hn : Primrec (fun x : ℕ=>(Nat.unpair (Nat.unpair x).1).1) :=
    Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have ha:=primitive_decodeCandidate.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
  have hp:=Primrec.fst.comp ha
  have hsource : Primrec (fun x : ℕ=>Nat.pair (2*(Nat.unpair (Nat.unpair x).1).1)
      (Nat.pair (Nat.unpair x).2 (decodeCandidate (Nat.unpair (Nat.unpair x).1).2).1)) :=
    Primrec₂.natPair.comp (Primrec.nat_mul.comp (Primrec.const 2) hn)
      (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.unpair) hp)
  have hs:=Oracle.comp (sourceState_recursive hc) (Oracle.of_computable hsource.to_comp)
  have hrad:=Oracle.comp hr (Oracle.of_computable
    (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.unpair) hp).to_comp)
  have harg:=Oracle.pair (Oracle.of_computable hn.to_comp)
    (Oracle.pair (Oracle.of_computable (Primrec.encode.comp ha).to_comp) (Oracle.pair hs hrad))
  let args : ℕ → EnclosureArgs := fun x=>
    ((Nat.unpair (Nat.unpair x).1).1,decodeCandidate (Nat.unpair (Nat.unpair x).1).2,
      sourceState centres (2*(Nat.unpair (Nat.unpair x).1).1) (Nat.unpair x).2
        (decodeCandidate (Nat.unpair (Nat.unpair x).1).2).1,
      radii (Nat.pair (Nat.unpair x).2 (decodeCandidate (Nat.unpair (Nat.unpair x).1).2).1))
  have hh:=applyEncoded (O:=O) (a:=args) primitive_enclosureFormula
    (harg.of_eq (fun x=>by simp only [Nat.unpair_pair,id_eq]; rfl))
  exact hh.of_eq fun x=>by
    simp only [args,enclosureFormula,PackingCodeJoint.coordinateFailure_eq,enclosureTerm,
      outerCode,outerRadiusCode,dimCode,sourceState]

private def cellK (x : ℕ) := (Nat.unpair (Nat.unpair (Nat.unpair x).1).1).1
private def cellStage (x : ℕ) := (Nat.unpair (Nat.unpair (Nat.unpair x).1).1).2
private def cellSource (x : ℕ) := (Nat.unpair (Nat.unpair x).1).2

/-- Layout `(((k,stage),source),grid)` keeps k in every query context. -/
def familyCellTerm (centres radii targets : ℕ → ℕ) (x : ℕ) : ℕ :=
  cellTerm centres radii (Family.slice targets (cellK x))
    (Nat.pair (Nat.pair (Nat.pair 2 (cellStage x)) (cellSource x)) (Nat.unpair x).2)

attribute [local irreducible] familyCellTerm

private theorem familyCellTerm_recursive {O : Set (ℕ →. ℕ)} {centres radii targets : ℕ → ℕ}
    (hc : Oracle.Total O centres) (hr : Oracle.Total O radii) (ht : Oracle.Total O targets) :
    Oracle.Total O (familyCellTerm centres radii targets) := by
  have hk : Primrec cellK := Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
  have hstage : Primrec cellStage := Primrec.snd.comp (Primrec.unpair.comp
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))))
  have hi : Primrec cellSource := Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have ha:=primitive_decodeCandidate.comp hstage
  have hp:=Primrec.fst.comp ha
  have hqsrc : Primrec (fun x=>Nat.pair 4 (Nat.pair (cellSource x) (decodeCandidate (cellStage x)).1)) :=
    Primrec₂.natPair.comp (Primrec.const 4) (Primrec₂.natPair.comp hi hp)
  have hs:=Oracle.comp (sourceState_recursive hc) (Oracle.of_computable hqsrc.to_comp)
  have hqrad:=Primrec₂.natPair.comp hi hp
  have hrad:=Oracle.comp hr (Oracle.of_computable hqrad.to_comp)
  have hqtarget : Primrec (fun x=>Nat.pair (cellK x) (decodeCandidate (cellStage x)).1) :=
    Primrec₂.natPair.comp hk hp
  have htarget:=Oracle.comp ht (Oracle.of_computable hqtarget.to_comp)
  have harg := Oracle.pair (Oracle.of_computable (O:=O) (Computable.const 2))
    (Oracle.pair (Oracle.of_computable (Primrec.encode.comp ha).to_comp)
      (Oracle.pair (Oracle.right (O:=O)) (Oracle.pair hs (Oracle.pair hrad htarget))))
  let args : ℕ → FormulaArgs := fun x=>
    (2,decodeCandidate (cellStage x),(Nat.unpair x).2,
      sourceState centres 4 (cellSource x) (decodeCandidate (cellStage x)).1,
      radii (Nat.pair (cellSource x) (decodeCandidate (cellStage x)).1),
      targets (Nat.pair (cellK x) (decodeCandidate (cellStage x)).1))
  have hh:=applyEncoded (O:=O) (a:=args) primitive_cellFormula
    (harg.of_eq (fun x=>by simp only [Nat.unpair_pair,id_eq]; rfl))
  exact hh.of_eq fun x=>by
    simp only [args,cellFormula,PackingCodeJoint.cellFailure_eq,PackingGridJoint.boxNodeCode_eq,
      familyCellTerm,cellK,cellStage,cellSource,cellTerm,outerCode,innerCode,
      outerRadiusCode,innerRadiusCode,dimCode,sourceState,Family.slice,Nat.unpair_pair]

private theorem familyCellTerm_at (centres radii targets : ℕ → ℕ) (k st i g : ℕ) :
    familyCellTerm centres radii targets (Nat.pair (Nat.pair (Nat.pair k st) i) g)=
      cellTerm centres radii (Family.slice targets k) (Nat.pair (Nat.pair (Nat.pair 2 st) i) g) := by
  simp only [familyCellTerm,cellK,cellStage,cellSource,Nat.unpair_pair]

private theorem sumFailure_congr_context {f g : ℕ → ℕ} {a b n : ℕ}
    (h : ∀ i,f (Nat.pair a i)=g (Nat.pair b i)) :
    sumFailure f a n=sumFailure g b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [sumFailure]
      rw [ih,h n]

/-- All grid nodes for one source, retaining the family parameter in the outer context. -/
def familySourceCells (centres radii targets : ℕ → ℕ) (x : ℕ) : ℕ :=
  sumFailure (familyCellTerm centres radii targets) x
    (FiniteGrid.count 4 (decodeCandidate (Nat.unpair (Nat.unpair x).1).2).2.2.2.1)

attribute [local irreducible] familySourceCells

private theorem familySourceCells_recursive {O : Set (ℕ →. ℕ)} {centres radii targets : ℕ → ℕ}
    (hc : Oracle.Total O centres) (hr : Oracle.Total O radii) (ht : Oracle.Total O targets) :
    Oracle.Total O (familySourceCells centres radii targets) := by
  have hstage : Primrec (fun x : ℕ=>(Nat.unpair (Nat.unpair x).1).2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have ha:=primitive_decodeCandidate.comp hstage
  have hm:=Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ha)))
  have hcount:=PackingGridJoint.primitive_count.comp ((Primrec.const 4).pair hm)
  have hh:=Oracle.comp (sumFailure_recursive (familyCellTerm_recursive hc hr ht))
    (Oracle.pair (Oracle.of_computable Computable.id) (Oracle.of_computable hcount.to_comp))
  exact hh.of_eq fun x=>by simp only [Nat.unpair_pair,familySourceCells,id_eq]

private theorem familySourceCells_at (centres radii targets : ℕ → ℕ) (k st i : ℕ) :
    familySourceCells centres radii targets (Nat.pair (Nat.pair k st) i)=
      sourceCells centres radii (Family.slice targets k) (Nat.pair (Nat.pair 2 st) i) := by
  simp only [familySourceCells,sourceCells,Nat.unpair_pair]
  apply sumFailure_congr_context
  intro g
  exact familyCellTerm_at centres radii targets k st i g

/-- One genuine joint computation for the family stage. -/
theorem stage_recursive {O : Set (ℕ →. ℕ)} {centres radii targets : ℕ → ℕ}
    (hc : Oracle.Total O centres) (hr : Oracle.Total O radii) (ht : Oracle.Total O targets) :
    Oracle.Total O (fun x=>stageFailure centres radii (Family.slice targets (Nat.unpair x).1)
      2 (Nat.unpair x).1 (Nat.unpair x).2) := by
  have hst : Primrec (fun x : ℕ=>(Nat.unpair x).2) := Primrec.snd.comp Primrec.unpair
  have hk : Primrec (fun x : ℕ=>(Nat.unpair x).1) := Primrec.fst.comp Primrec.unpair
  have hctx:=Primrec₂.natPair.comp (Primrec.const 2) hst
  have hE:=Oracle.comp (sumFailure_recursive (enclosureTerm_recursive hc hr))
    (Oracle.of_computable (Primrec₂.natPair.comp hctx hk).to_comp)
  have hC:=Oracle.comp (sumFailure_recursive (familySourceCells_recursive hc hr ht))
    (Oracle.pair (Oracle.of_computable Computable.id) (Oracle.of_computable hk.to_comp))
  have ha:=primitive_decodeCandidate.comp hst
  have hB:=Primrec.fst.comp (Primrec.snd.comp ha)
  have hQ:=Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hN:=Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ha))))
  have hg : Primrec (fun x : ℕ=>if 0<(decodeCandidate (Nat.unpair x).2).2.1 ∧
      0<(decodeCandidate (Nat.unpair x).2).2.2.1 ∧
      0<(decodeCandidate (Nat.unpair x).2).2.2.2.2.1 then 0 else 1) :=
    Primrec.ite ((Primrec.nat_lt.comp (Primrec.const 0) hB).and
      ((Primrec.nat_lt.comp (Primrec.const 0) hQ).and (Primrec.nat_lt.comp (Primrec.const 0) hN)))
      (Primrec.const 0) (Primrec.const 1)
  have hh:=Oracle.comp (Oracle.addPair (O:=O))
    (Oracle.pair (Oracle.comp (Oracle.addPair (O:=O))
      (Oracle.pair (Oracle.of_computable hg.to_comp) hE)) hC)
  exact hh.of_eq fun x=>by
    have hs : sumFailure (familySourceCells centres radii targets) x (Nat.unpair x).1=
        sumFailure (sourceCells centres radii (Family.slice targets (Nat.unpair x).1))
          (Nat.pair 2 (Nat.unpair x).2) (Nat.unpair x).1 := by
      apply sumFailure_congr_context
      intro i
      have heq := familySourceCells_at centres radii targets (Nat.unpair x).1 (Nat.unpair x).2 i
      simpa only [Nat.pair_unpair] using heq
    simp only [Nat.unpair_pair,stageFailure,id_eq]
    rw [hs]

end SymplecticPacking.Effective.PackingSearch.EpochRuntime

namespace SymplecticPacking.Effective.PackingSearch

attribute [local irreducible] stageFailure sourceCells cellTerm enclosureTerm PackingSearchInput.sourceState decodeCandidate programCode

/-- The radius-family query is indexed by the same runtime k as the finite source loop. -/
def familyStageFailure (centres radii targets : ℕ → ℕ) (k st : ℕ) : ℕ :=
  stageFailure centres radii (Family.slice targets k) 2 k st

theorem familyStageFailure_recursive {O : Set (ℕ →. ℕ)} {centres radii targets : ℕ → ℕ}
    (hc : Oracle.Total O centres) (hr : Oracle.Total O radii) (ht : Oracle.Total O targets) :
    Oracle.Total O (fun x=>familyStageFailure centres radii targets (Nat.unpair x).1 (Nat.unpair x).2) :=
  EpochRuntime.stage_recursive hc hr ht

def familyPartialSearch (centres radii targets : ℕ → ℕ) (k : ℕ) : Part ℕ :=
  Nat.rfind (fun st=>Part.some (decide (familyStageFailure centres radii targets k st=0)))

theorem familyPartialSearch_recursive {O : Set (ℕ →. ℕ)} {centres radii targets : ℕ → ℕ}
    (hc : Oracle.Total O centres) (hr : Oracle.Total O radii) (ht : Oracle.Total O targets) :
    Nat.RecursiveIn O (familyPartialSearch centres radii targets) := by
  have h:=Nat.RecursiveIn.rfind (familyStageFailure_recursive hc hr ht)
  exact h.of_eq fun a=>by simp only [Nat.unpair_pair,Part.map_some];rfl

theorem familyPartialSearch_halts {centres radii targets : ℕ → ℕ} {k : ℕ}
    (hex : ∃ st,familyStageFailure centres radii targets k st=0) :
    Nat.find hex ∈ familyPartialSearch centres radii targets k := by
  apply Nat.mem_rfind.mpr
  refine ⟨?_,?_⟩
  · exact Part.mem_some_iff.mpr (decide_eq_true (Nat.find_spec hex)).symm
  · intro m hm
    simp [Nat.find_min hex hm]

def familyProgramSearch (centres radii targets : ℕ → ℕ) (k : ℕ) : Part ℕ :=
  (familyPartialSearch centres radii targets k).map programCode

theorem familyProgramSearch_recursive {O : Set (ℕ →. ℕ)} {centres radii targets : ℕ → ℕ}
    (hc : Oracle.Total O centres) (hr : Oracle.Total O radii) (ht : Oracle.Total O targets) :
    Nat.RecursiveIn O (familyProgramSearch centres radii targets) := by
  have h:=Nat.RecursiveIn.comp (Oracle.of_computable (O:=O) primitive_programCode.to_comp)
    (familyPartialSearch_recursive hc hr ht)
  exact h.of_eq fun a=>Part.bind_some_eq_map programCode (familyPartialSearch centres radii targets a)

theorem familyProgramSearch_halts {centres radii targets : ℕ → ℕ} {k : ℕ}
    (hex : ∃ st,familyStageFailure centres radii targets k st=0) :
    programCode (Nat.find hex) ∈ familyProgramSearch centres radii targets k :=
  Part.mem_map programCode (familyPartialSearch_halts hex)

#check_explicit familyProgramSearch
end SymplecticPacking.Effective.PackingSearch
