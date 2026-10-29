import SymplecticPacking.Effective.PackingCertificateCode
import SymplecticPacking.Effective.PackingCertificateStateList

/-!
# Finite rational tests in a runtime dimension

Finite rational tests with dimension as natural-number input.
-/

namespace SymplecticPacking.Effective.PackingCodeJoint
open RationalCode
open PackingCertificateCode (sumCodes primitive_sumCodes dimCode primitive_dimCode)

private theorem map_range (d : ℕ) (f : ℕ → ℕ) :
    (List.range d).map f=List.ofFn (fun j : Fin d => f j.val) := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp

private theorem coordinate_fin (d state : ℕ) (j : Fin d) :
    PackingStateList.coordinate d state j.val=ODECode.decodeState d state j := by
  rw [PackingStateList.coordinate_eq_decode]
  simp

private theorem primitive_coordinate_comp {α : Type*} [Primcodable α]
    {d s i : α → ℕ} (hd : Primrec d) (hs : Primrec s) (hi : Primrec i) :
    Primrec (fun a => PackingStateList.coordinate (d a) (s a) (i a)) :=
  PackingStateList.primitive_coordinate.comp (hd.pair (hs.pair hi))

private theorem primitive_mapState {α : Type*} [Primcodable α]
    {d s : α → ℕ} {f : α → ℕ → ℕ}
    (hd : Primrec d) (hs : Primrec s) (hf : Primrec₂ f) :
    Primrec (fun a => (PackingStateList.stateList (d a) (s a)).map (f a)) :=
  Primrec.list_map (PackingStateList.primitive_stateList.comp (hd.pair hs)) hf

private theorem primitive_mapRange {α : Type*} [Primcodable α]
    {d : α → ℕ} {f : α → ℕ → ℕ} (hd : Primrec d) (hf : Primrec₂ f) :
    Primrec (fun a => (List.range (d a)).map (f a)) :=
  Primrec.list_map (Primrec.list_range.comp hd) hf

private theorem primitive_sum : Primrec (List.sum : List ℕ → ℕ) :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

def squareNormCode (d state : ℕ) : ℕ := sumCodes
  ((PackingStateList.stateList d state).map (fun u => mulCode u u))

@[irreducible] def distanceCode (d state source : ℕ) : ℕ := sumCodes ((List.range d).map (fun j =>
  let u := addCode (PackingStateList.coordinate d state j)
    (negCode (PackingStateList.coordinate d source j))
  mulCode u u))

def coordinateFailure (d state e R : ℕ) : ℕ :=
  ((PackingStateList.stateList d state).map (fun u =>
    if Less (addCode (absCode u) e) R then 0 else 1)).sum

def targetFailure (d state e R : ℕ) : ℕ :=
  if Less zeroCode (PackingCertificateCode.targetMargin d e R) ∧
    Less (squareNormCode d state)
      (mulCode (PackingCertificateCode.targetMargin d e R) (PackingCertificateCode.targetMargin d e R))
  then 0 else 1

def outsideFailure (d state source ρ r : ℕ) : ℕ :=
  let margin := addCode r (mulCode (dimCode d) ρ)
  if Less (mulCode margin margin) (distanceCode d state source) then 0 else 1

theorem squareNormCode_eq (d state : ℕ) : squareNormCode d state=PackingCertificateCode.squareNormCode d state := by
  rw [squareNormCode,←PackingStateList.decodeState_eq_list,List.map_ofFn]
  rfl

theorem distanceCode_eq (d state source : ℕ) :
    distanceCode d state source=PackingCertificateCode.distanceCode d state source := by
  rw [distanceCode,map_range]
  simp only [coordinate_fin,PackingCertificateCode.distanceCode]

theorem coordinateFailure_eq (d state e R : ℕ) :
    coordinateFailure d state e R=PackingCertificateCode.coordinateFailure d state e R := by
  rw [coordinateFailure,PackingCertificateCode.coordinateFailure,←PackingStateList.decodeState_eq_list,List.map_ofFn]
  simp only [Function.comp_def]

theorem targetFailure_eq (d state e R : ℕ) : targetFailure d state e R=PackingCertificateCode.targetFailure d state e R := by
  simp only [targetFailure,squareNormCode_eq,PackingCertificateCode.targetFailure]

theorem outsideFailure_eq (d state source ρ r : ℕ) :
    outsideFailure d state source ρ r=PackingCertificateCode.outsideFailure d state source ρ r := by
  simp only [outsideFailure,distanceCode_eq,PackingCertificateCode.outsideFailure]

theorem primitive_squareNormCode : Primrec (fun a : ℕ × ℕ => squareNormCode a.1 a.2) := by
  have hm : Primrec (fun a : ℕ × ℕ => (PackingStateList.stateList a.1 a.2).map (fun u => mulCode u u)) :=
    primitive_mapState Primrec.fst Primrec.snd
      ((primitive_mulCode.comp Primrec.snd Primrec.snd).to₂)
  exact (primitive_sumCodes.comp hm).of_eq (fun _ => rfl)

theorem primitive_distanceCode : Primrec (fun a : ℕ × (ℕ × ℕ) => distanceCode a.1 a.2.1 a.2.2) := by
  have hx : Primrec (fun p : (ℕ × (ℕ × ℕ)) × ℕ => PackingStateList.coordinate p.1.1 p.1.2.1 p.2) :=
    primitive_coordinate_comp (Primrec.fst.comp Primrec.fst)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  have hs : Primrec (fun p : (ℕ × (ℕ × ℕ)) × ℕ => PackingStateList.coordinate p.1.1 p.1.2.2 p.2) :=
    primitive_coordinate_comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  have hu := primitive_addCode.comp hx (primitive_negCode.comp hs)
  have hm := primitive_mapRange Primrec.fst (primitive_mulCode.comp hu hu).to₂
  unfold distanceCode
  exact (primitive_sumCodes.comp hm).of_eq (fun _ => rfl)

attribute [local irreducible] PackingCertificateCode.targetMargin

theorem primitive_targetMargin :
    Primrec (fun a : ℕ × (ℕ × ℕ) => PackingCertificateCode.targetMargin a.1 a.2.1 a.2.2) := by
  unfold PackingCertificateCode.targetMargin
  exact primitive_addCode.comp (Primrec.snd.comp Primrec.snd)
    (primitive_negCode.comp (primitive_mulCode.comp (primitive_dimCode.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)))

theorem primitive_coordinateFailure :
    Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => coordinateFailure a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  have test (u v w : (ℕ × (ℕ × (ℕ × ℕ))) × ℕ → ℕ)
      (hu : Primrec u) (hv : Primrec v) (hw : Primrec w) :
      Primrec (fun a => if Less (addCode (absCode (u a)) (v a)) (w a) then 0 else 1) :=
    Primrec.ite (primitive_less.comp (primitive_addCode.comp (primitive_absCode.comp hu) hv) hw)
      (Primrec.const 0) (Primrec.const 1)
  have hf : Primrec (fun p : (ℕ × (ℕ × (ℕ × ℕ))) × ℕ =>
      if Less (addCode (absCode p.2) p.1.2.2.1) p.1.2.2.2 then 0 else 1) :=
    test _ _ _ Primrec.snd
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hm := primitive_mapState Primrec.fst (Primrec.fst.comp Primrec.snd) hf.to₂
  exact (primitive_sum.comp hm).of_eq (fun _ => rfl)

private theorem primitive_margin_comp {α : Type*} [Primcodable α] {d e r : α → ℕ}
    (hd : Primrec d) (he : Primrec e) (hr : Primrec r) :
    Primrec (fun a => PackingCertificateCode.targetMargin (d a) (e a) (r a)) :=
  (primitive_targetMargin.comp (hd.pair (he.pair hr))).of_eq (fun _ => rfl)

private theorem primitive_square_comp {α : Type*} [Primcodable α] {d s : α → ℕ}
    (hd : Primrec d) (hs : Primrec s) : Primrec (fun a => squareNormCode (d a) (s a)) :=
  primitive_squareNormCode.comp (hd.pair hs)

private theorem primitive_distance_comp {α : Type*} [Primcodable α] {d s t : α → ℕ}
    (hd : Primrec d) (hs : Primrec s) (ht : Primrec t) :
    Primrec (fun a => distanceCode (d a) (s a) (t a)) :=
  (primitive_distanceCode.comp (hd.pair (hs.pair ht))).of_eq (fun _ => rfl)

theorem primitive_targetFailure :
    Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => targetFailure a.1 a.2.1 a.2.2.1 a.2.2.2) := by
  have hm : Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) =>
      PackingCertificateCode.targetMargin a.1 a.2.2.1 a.2.2.2) :=
    primitive_margin_comp Primrec.fst
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hs : Primrec (fun a : ℕ × (ℕ × (ℕ × ℕ)) => squareNormCode a.1 a.2.1) :=
    primitive_square_comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  unfold targetFailure
  exact Primrec.ite ((primitive_less.comp (Primrec.const zeroCode) hm).and
    (primitive_less.comp hs (primitive_mulCode.comp hm hm))) (Primrec.const 0) (Primrec.const 1)

theorem primitive_outsideFailure :
    Primrec (fun a : ℕ × ((ℕ × ℕ) × (ℕ × ℕ)) =>
      outsideFailure a.1 a.2.1.1 a.2.1.2 a.2.2.1 a.2.2.2) := by
  have compose (u v : ℕ × ((ℕ × ℕ) × (ℕ × ℕ)) → ℕ) (hu : Primrec u) (hv : Primrec v) :
      Primrec (fun a => if Less (u a) (v a) then 0 else 1) :=
    Primrec.ite (primitive_less.comp hu hv) (Primrec.const 0) (Primrec.const 1)
  have hm : Primrec (fun a : ℕ × ((ℕ × ℕ) × (ℕ × ℕ)) =>
      addCode a.2.2.2 (mulCode (dimCode a.1) a.2.2.1)) :=
    primitive_addCode.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      (primitive_mulCode.comp (primitive_dimCode.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  have hd : Primrec (fun a : ℕ × ((ℕ × ℕ) × (ℕ × ℕ)) => distanceCode a.1 a.2.1.1 a.2.1.2) :=
    primitive_distance_comp Primrec.fst
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  unfold outsideFailure
  exact compose _ _ (primitive_mulCode.comp hm hm) hd

end SymplecticPacking.Effective.PackingCodeJoint
