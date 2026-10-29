import SymplecticPacking.Effective.PackingCertificateCodeJointCore
import SymplecticPacking.Effective.PackingCertificateFieldJoint

/-!
# Exact Euler verification in a runtime dimension

Exact Euler verification with dimension and every candidate parameter as input.
-/

namespace SymplecticPacking.Effective.PackingCodeJoint
open RationalCode
attribute [local irreducible] PackingPolynomialJoint.universalField coordinateFailure targetFailure outsideFailure

private theorem coordinate_fin (d state : ℕ) (j : Fin d) :
    PackingStateList.coordinate d state j.val=ODECode.decodeState d state j := by
  rw [PackingStateList.coordinate_eq_decode]
  simp

private theorem map_range (d : ℕ) (f : ℕ → ℕ) :
    (List.range d).map f=List.ofFn (fun j : Fin d => f j.val) := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp

private theorem primitive_coordinate_comp {α : Type*} [Primcodable α]
    {d s i : α → ℕ} (hd : Primrec d) (hs : Primrec s) (hi : Primrec i) :
    Primrec (fun a => PackingStateList.coordinate (d a) (s a) (i a)) :=
  PackingStateList.primitive_coordinate.comp (hd.pair (hs.pair hi))

@[irreducible] def update (d N state velocity : ℕ) : ℕ := Encodable.encode ((List.range d).map (fun j =>
  addCode (PackingStateList.coordinate d state j)
    (divideNatCode (PackingStateList.coordinate d velocity j) (N-1))))

@[irreducible] def step (n N candidate i state : ℕ) : ℕ := update (2*n) N state
  (PackingPolynomialJoint.universalField n
    (Nat.pair (ODECode.timeCode N i) (Nat.pair state candidate)))

@[irreducible] def iterate (n N candidate initial i : ℕ) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) initial (fun j state => step n N candidate j state) i

theorem iterate_zero (n N candidate initial : ℕ) : iterate n N candidate initial 0=initial := by
  unfold iterate
  rfl

theorem iterate_succ (n N candidate initial i : ℕ) :
    iterate n N candidate initial (i+1)=step n N candidate i (iterate n N candidate initial i) := by
  unfold iterate
  rfl

theorem update_eq (d N state velocity : ℕ) : update d N state velocity=
    ODECode.encodeState d (ODECode.update d N (ODECode.decodeState d state) (ODECode.decodeState d velocity)) := by
  rw [update,PackingStateList.encodeState_eq_list,map_range]
  simp only [coordinate_fin]
  unfold ODECode.update
  rfl

theorem step_eq (n N candidate i state : ℕ) : step n N candidate i state=
    ODECode.step (2*n) N candidate (PackingPolynomialCode.universalField n) i state := by
  simp only [step,update_eq,PackingPolynomialJoint.universalField_eq,ODECode.step,ODECode.encodeState]

theorem iterate_eq (n N candidate initial i : ℕ) : iterate n N candidate initial i=
    ODECode.iterate (2*n) N candidate (PackingPolynomialCode.universalField n) initial i := by
  induction i with
  | zero => rw [iterate_zero,ODECode.iterate]
  | succ i ih => rw [iterate_succ,ODECode.iterate,step_eq,ih]

theorem primitive_update :
    Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => update a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  have hx : Primrec (fun p : (ℕ × (ℕ × (ℕ × ℕ))) × ℕ =>
      PackingStateList.coordinate p.1.1 p.1.2.2.1 p.2) :=
    primitive_coordinate_comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd
  have hv : Primrec (fun p : (ℕ × (ℕ × (ℕ × ℕ))) × ℕ =>
      PackingStateList.coordinate p.1.1 p.1.2.2.2 p.2) :=
    primitive_coordinate_comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd
  have hN : Primrec (fun p : (ℕ × (ℕ × (ℕ × ℕ))) × ℕ => p.1.2.1-1) :=
    Primrec.nat_sub.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const 1)
  have hc := primitive_addCode.comp hx (primitive_divideNatCode.comp hv hN)
  have hm := Primrec.list_map (Primrec.list_range.comp Primrec.fst) hc.to₂
  unfold update
  exact (Primrec.encode.comp hm).of_eq (fun _ => rfl)

theorem primitive_step :
    Primrec (fun a : ℕ × (ℕ × (ℕ × (ℕ × ℕ))) => step a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2) := by
  have hn : Primrec (fun a : ℕ × (ℕ × (ℕ × (ℕ × ℕ))) => a.1) := Primrec.fst
  have hN : Primrec (fun a : ℕ × (ℕ × (ℕ × (ℕ × ℕ))) => a.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun a : ℕ × (ℕ × (ℕ × (ℕ × ℕ))) => a.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hi : Primrec (fun a : ℕ × (ℕ × (ℕ × (ℕ × ℕ))) => a.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hs : Primrec (fun a : ℕ × (ℕ × (ℕ × (ℕ × ℕ))) => a.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hquery := Primrec₂.natPair.comp (ODECode.primitive_timeCode.comp hN hi)
    (Primrec₂.natPair.comp hs hc)
  have hf := PackingPolynomialJoint.primitive_universalField.comp (hn.pair hquery)
  have hd := Primrec.nat_mul.comp (Primrec.const 2) hn
  unfold step
  exact primitive_update.comp (hd.pair (hN.pair (hs.pair hf)))

theorem primitive_iterate :
    Primrec (fun a : (ℕ × (ℕ × (ℕ × ℕ))) × ℕ =>
      iterate a.1.1 a.1.2.1 a.1.2.2.1 a.1.2.2.2 a.2) := by
  have hs : Primrec (fun p : (ℕ × (ℕ × (ℕ × ℕ))) × (ℕ × ℕ) =>
      step p.1.1 p.1.2.1 p.1.2.2.1 p.2.1 p.2.2) :=
    primitive_step.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
          ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd)))))
  have hinit : Primrec (fun p : ℕ × (ℕ × (ℕ × ℕ)) => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hloop : Primrec (fun a : (ℕ × (ℕ × (ℕ × ℕ))) × ℕ =>
      Nat.rec (motive := fun _ => ℕ) a.1.2.2.2
        (fun i state => step a.1.1 a.1.2.1 a.1.2.2.1 i state) a.2) :=
    Primrec.nat_rec hinit hs.to₂
  exact hloop.of_eq fun a => by
    unfold iterate
    rfl

@[irreducible] def iteration (n a i : ℕ) : ℕ := iterate n (Nat.unpair (Nat.unpair a).1).1
  (Nat.unpair (Nat.unpair a).1).2 (Nat.unpair a).2 i

@[irreducible] def rowFailure (n b : ℕ) : ℕ := coordinateFailure (2*n)
  (iteration n (Nat.unpair (Nat.unpair b).1).1 (Nat.unpair b).2)
  (Nat.unpair (Nat.unpair (Nat.unpair b).1).2).1
  (Nat.unpair (Nat.unpair (Nat.unpair b).1).2).2

@[irreducible] def tubeFailure (n a : ℕ) : ℕ := PackingCertificateCode.sumFailure (rowFailure n) a
  ((Nat.unpair (Nat.unpair (Nat.unpair a).1).1).1+1)

theorem iteration_eq (n a i : ℕ) : iteration n a i=
    PackingCertificateCode.iteration (2*n) (PackingPolynomialCode.universalField n) a i := by
  simp only [iteration,iterate_eq,PackingCertificateCode.iteration]

theorem rowFailure_eq (n b : ℕ) : rowFailure n b=
    PackingCertificateCode.rowFailure (2*n) (PackingPolynomialCode.universalField n) b := by
  simp only [rowFailure,coordinateFailure_eq,iteration_eq,PackingCertificateCode.rowFailure]

theorem tubeFailure_eq (n a : ℕ) : tubeFailure n a=
    PackingCertificateCode.tubeFailure (2*n) (PackingPolynomialCode.universalField n) a := by
  rw [tubeFailure]
  have hr : rowFailure n=PackingCertificateCode.rowFailure (2*n) (PackingPolynomialCode.universalField n) :=
    funext (rowFailure_eq n)
  rw [hr]
  rfl

theorem primitive_iteration : Primrec (fun a : ℕ × (ℕ × ℕ) => iteration a.1 a.2.1 a.2.2) := by
  have hn : Primrec (fun a : ℕ × (ℕ × ℕ) => a.1) := Primrec.fst
  have ha : Primrec (fun a : ℕ × (ℕ × ℕ) => a.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun a : ℕ × (ℕ × ℕ) => a.2.2) := Primrec.snd.comp Primrec.snd
  have hu := Primrec.unpair.comp ha
  have hv := Primrec.unpair.comp (Primrec.fst.comp hu)
  unfold iteration
  exact primitive_iterate.comp ((hn.pair ((Primrec.fst.comp hv).pair
    ((Primrec.snd.comp hv).pair (Primrec.snd.comp hu)))).pair hi)

theorem primitive_rowFailure : Primrec (fun a : ℕ × ℕ => rowFailure a.1 a.2) := by
  have hn : Primrec (fun a : ℕ × ℕ => a.1) := Primrec.fst
  have hb : Primrec (fun a : ℕ × ℕ => a.2) := Primrec.snd
  have hu := Primrec.unpair.comp hb
  have hv := Primrec.unpair.comp (Primrec.fst.comp hu)
  have hr := Primrec.unpair.comp (Primrec.snd.comp hv)
  have hs := primitive_iteration.comp (hn.pair ((Primrec.fst.comp hv).pair (Primrec.snd.comp hu)))
  unfold rowFailure
  exact primitive_coordinateFailure.comp
    ((Primrec.nat_mul.comp (Primrec.const 2) hn).pair
      (hs.pair ((Primrec.fst.comp hr).pair (Primrec.snd.comp hr))))

theorem primitive_sum_rows : Primrec (fun a : (ℕ × ℕ) × ℕ =>
    PackingCertificateCode.sumFailure (rowFailure a.1.1) a.1.2 a.2) := by
  have hs : Primrec (fun a : (ℕ × ℕ) × (ℕ × ℕ) =>
      a.2.2+rowFailure a.1.1 (Nat.pair a.1.2 a.2.1)) :=
    Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd)
      (primitive_rowFailure.comp ((Primrec.fst.comp Primrec.fst).pair
        (Primrec₂.natPair.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))))
  have hh : Primrec (fun a : (ℕ × ℕ) × ℕ =>
      Nat.rec (motive := fun _ => ℕ) 0 (fun i acc => acc+rowFailure a.1.1 (Nat.pair a.1.2 i)) a.2) :=
    Primrec.nat_rec (Primrec.const 0) hs.to₂
  exact hh.of_eq fun a => by
    induction a.2 with
    | zero => rfl
    | succ i ih => simp only [PackingCertificateCode.sumFailure,ih]

theorem primitive_tubeFailure : Primrec (fun a : ℕ × ℕ => tubeFailure a.1 a.2) := by
  have hn : Primrec (fun a : ℕ × ℕ => a.1) := Primrec.fst
  have ha : Primrec (fun a : ℕ × ℕ => a.2) := Primrec.snd
  have hN := Primrec.succ.comp (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp (Primrec.unpair.comp ha))))))
  unfold tubeFailure
  exact primitive_sum_rows.comp ((hn.pair ha).pair hN)

@[irreducible] def cellFailure (n N candidate initial source ρ r e plateau target : ℕ) : ℕ :=
  if outsideFailure (2*n) initial source ρ r=0 then 0 else
    tubeFailure n (Nat.pair (Nat.pair (Nat.pair N candidate) initial) (Nat.pair e plateau))+
      targetFailure (2*n) (iterate n N candidate initial N) e target

theorem cellFailure_eq (n N candidate initial source ρ r e plateau target : ℕ) :
    cellFailure n N candidate initial source ρ r e plateau target=
      PackingCertificateCode.cellFailure (2*n) (PackingPolynomialCode.universalField n)
        N candidate initial source ρ r e plateau target := by
  simp only [cellFailure,outsideFailure_eq,tubeFailure_eq,targetFailure_eq,iterate_eq,
    PackingCertificateCode.cellFailure,PackingCertificateCode.iteration,Nat.unpair_pair]

abbrev CellArgs := ℕ × (ℕ × (ℕ × (ℕ × (ℕ × (ℕ × (ℕ × (ℕ × (ℕ × ℕ))))))))

theorem primitive_cellFailure : Primrec (fun a : CellArgs => cellFailure a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.2.1 a.2.2.2.2.2.2.2.2.2) := by
  have h0 : Primrec (fun a : CellArgs => a.1) := Primrec.fst
  have h1 : Primrec (fun a : CellArgs => a.2.1) := (Primrec.fst).comp Primrec.snd
  have h2 : Primrec (fun a : CellArgs => a.2.2.1) := ((Primrec.fst).comp Primrec.snd).comp Primrec.snd
  have h3 : Primrec (fun a : CellArgs => a.2.2.2.1) := (((Primrec.fst).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
  have h4 : Primrec (fun a : CellArgs => a.2.2.2.2.1) := ((((Primrec.fst).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
  have h5 : Primrec (fun a : CellArgs => a.2.2.2.2.2.1) := (((((Primrec.fst).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
  have h6 : Primrec (fun a : CellArgs => a.2.2.2.2.2.2.1) := ((((((Primrec.fst).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
  have h7 : Primrec (fun a : CellArgs => a.2.2.2.2.2.2.2.1) := (((((((Primrec.fst).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
  have h8 : Primrec (fun a : CellArgs => a.2.2.2.2.2.2.2.2.1) := ((((((((Primrec.fst).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
  have h9 : Primrec (fun a : CellArgs => a.2.2.2.2.2.2.2.2.2) := (((((((((Primrec.id).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd).comp Primrec.snd
  have hd := Primrec.nat_mul.comp (Primrec.const 2) h0
  have ho := primitive_outsideFailure.comp (hd.pair ((h3.pair h4).pair (h5.pair h6)))
  have htcode := Primrec₂.natPair.comp
    (Primrec₂.natPair.comp (Primrec₂.natPair.comp h1 h2) h3) (Primrec₂.natPair.comp h7 h8)
  have ht := primitive_tubeFailure.comp (h0.pair htcode)
  have hi := primitive_iterate.comp ((h0.pair (h1.pair (h2.pair h3))).pair h1)
  have hg := primitive_targetFailure.comp (hd.pair (hi.pair (h7.pair h9)))
  have combine (u v w : CellArgs → ℕ) (hu : Primrec u) (hv : Primrec v) (hw : Primrec w) :
      Primrec (fun a => if u a=0 then 0 else v a+w a) :=
    Primrec.ite (Primrec.eq.comp hu (Primrec.const 0)) (Primrec.const 0) (Primrec.nat_add.comp hv hw)
  unfold cellFailure
  exact combine _ _ _ ho ht hg

end SymplecticPacking.Effective.PackingCodeJoint
