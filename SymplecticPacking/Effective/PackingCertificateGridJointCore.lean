import SymplecticPacking.Effective.PackingCertificateGrid

/-!
# The grid machine in a runtime dimension

One finite grid machine with dimension as runtime input.
-/

namespace SymplecticPacking.Effective.PackingGridJoint
open RationalCode

/-- The closed formula for the original least-significant-first digits. -/
theorem digits_closed (d b i : ℕ) (j : Fin d) :
    FiniteGrid.digits d b i j = i / b^j.val % b := by
  induction d generalizing i with
  | zero => exact Fin.elim0 j
  | succ d ih =>
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [FiniteGrid.digits]
      · rw [FiniteGrid.digits,Fin.cases_succ,ih]
        simp only [Fin.val_succ,Nat.pow_succ,Nat.div_div_eq_div_mul]
        rw [Nat.mul_comm]

/-- Exactly the original coordinate code, with a natural coordinate index. -/
def coordinate (Q m i j : ℕ) : ℕ :=
  addCode (mulCode (encode (2*Q) 0 0)
    (ODECode.timeCode (FiniteGrid.size m) (i/(FiniteGrid.size m+1)^j%(FiniteGrid.size m+1))))
    (negCode (encode Q 0 0))

def boxNodeCodes (d Q m i : ℕ) : List ℕ := (List.range d).map (coordinate Q m i)
def boxNodeCode (d Q m i : ℕ) : ℕ := Encodable.encode (boxNodeCodes d Q m i)

theorem coordinate_eq (d Q m i : ℕ) (j : Fin d) :
    coordinate Q m i j.val=PackingCertificate.boxNodeState d Q m i j := by
  rw [PackingCertificate.boxNodeState,FiniteGrid.code_decode]
  simp only [coordinate,FiniteGrid.nodeCodes,digits_closed]

theorem boxNodeCodes_eq (d Q m i : ℕ) :
    boxNodeCodes d Q m i=List.ofFn (PackingCertificate.boxNodeState d Q m i) := by
  apply List.ext_getElem
  · simp [boxNodeCodes]
  · intro j hj hj'
    simp only [boxNodeCodes,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    exact coordinate_eq d Q m i ⟨j,by simpa only [List.length_ofFn] using hj'⟩


theorem primitive_coordinate :
    Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => coordinate a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  have hm : Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => a.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => a.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hj : Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => a.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hsize := FiniteGrid.primitive_size.comp hm
  have hb := Primrec.nat_add.comp hsize (Primrec.const 1)
  have hpow := (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp hb hj
  have hdigit := Primrec.nat_mod.comp (Primrec.nat_div.comp hi hpow) hb
  have hnode := ODECode.primitive_timeCode.comp hsize hdigit
  have hQ : Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => encode a.1 0 0) :=
    Primrec₂.natPair.comp (Primrec₂.natPair.comp Primrec.fst (Primrec.const 0)) (Primrec.const 0)
  have h2Q : Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => encode (2*a.1) 0 0) :=
    Primrec₂.natPair.comp (Primrec₂.natPair.comp
      (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst) (Primrec.const 0)) (Primrec.const 0)
  exact primitive_addCode.comp (primitive_mulCode.comp h2Q hnode) (primitive_negCode.comp hQ)

theorem primitive_boxNodeCodes :
    Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => boxNodeCodes a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  have hargs : Primrec (fun p : (ℕ × (ℕ × (ℕ × ℕ))) × ℕ =>
      (p.1.2.1,(p.1.2.2.1,(p.1.2.2.2,p.2)))) :=
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
        ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd))
  have hc := primitive_coordinate.comp hargs
  exact Primrec.list_map (Primrec.list_range.comp Primrec.fst) hc.to₂

theorem primitive_boxNodeCode :
    Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => boxNodeCode a.1 a.2.1 a.2.2.1 a.2.2.2) :=
  (Primrec.encode.comp primitive_boxNodeCodes).of_eq (fun _ => rfl)

theorem primitive_count : Primrec (fun a : ℕ × ℕ => FiniteGrid.count a.1 a.2) :=
  (Primrec₂.unpaired'.mp Nat.Primrec.pow).comp
    (Primrec.nat_add.comp (FiniteGrid.primitive_size.comp Primrec.snd) (Primrec.const 1)) Primrec.fst

end SymplecticPacking.Effective.PackingGridJoint
