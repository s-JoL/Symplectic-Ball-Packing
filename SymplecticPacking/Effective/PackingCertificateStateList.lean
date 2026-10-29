import SymplecticPacking.Effective.ODECode

/-!
# Vectors of runtime length as natural-number states

A single natural-number machine for vectors of runtime length.
-/

namespace SymplecticPacking.Effective.PackingStateList
open RationalCode
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def decodeList (code : ℕ) : List ℕ := (Encodable.decode (α:=List ℕ) code).getD []

theorem primitive_decodeList : Primrec decodeList :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

/-- Malformed vector codes denote the zero vector of the requested length. -/
def stateList (d code : ℕ) : List ℕ :=
  let xs := decodeList code
  if xs.length=d then xs else List.replicate d zeroCode

theorem encodeState_eq_list (d : ℕ) (x : ODECode.State d) :
    ODECode.encodeState d x=Encodable.encode (List.ofFn x) := by
  change Encodable.encode (List.Vector.ofFn x).toList = Encodable.encode (List.ofFn x)
  exact congrArg Encodable.encode (List.Vector.toList_ofFn x)

private theorem decodeVectorList_aux (d : ℕ) (o : Option (List ℕ)) :
    List.ofFn ((Option.map (fun v : List.Vector ℕ d => v.get)
      (o.bind (fun xs => if h : xs.length=d then some (⟨xs,h⟩ : List.Vector ℕ d) else none))).getD
      (fun _ => zeroCode)) =
      if (o.getD []).length=d then o.getD [] else List.replicate d zeroCode := by
  cases o with
  | none =>
    simp only [Option.bind_none,Option.map_none,Option.getD_none,List.length_nil]
    split_ifs with hh
    · have hd : d=0 := hh.symm
      subst d
      rfl
    · simp
  | some xs =>
    by_cases hx : xs.length=d
    · simp only [Option.bind_some,dif_pos hx,Option.map_some,Option.getD_some,if_pos hx]
      let v : List.Vector ℕ d := ⟨xs,hx⟩
      calc
        List.ofFn v.get = (List.Vector.ofFn v.get).toList :=
          (List.Vector.toList_ofFn v.get).symm
        _ = v.toList := congrArg List.Vector.toList (List.Vector.ofFn_get v)
        _ = xs := rfl
    · simp only [Option.bind_some,dif_neg hx,Option.map_none,Option.getD_none,Option.getD_some,if_neg hx]
      simp

theorem decodeState_eq_list (d code : ℕ) :
    List.ofFn (ODECode.decodeState d code)=stateList d code := by
  dsimp only [stateList,decodeList]
  letI : Encodable (List.Vector ℕ d) := Primcodable.toEncodable
  unfold ODECode.decodeState
  change List.ofFn ((@Encodable.decode _ (Encodable.ofEquiv (List.Vector ℕ d)
    (Equiv.vectorEquivFin ℕ d).symm) code).getD (fun _ => zeroCode)) = _
  rw [Encodable.decode_ofEquiv]
  change List.ofFn ((Option.map (fun v : List.Vector ℕ d => v.get)
    ((Encodable.decode (α:=List ℕ) code).bind (fun xs =>
      if h : xs.length=d then some ⟨xs,h⟩ else none))).getD (fun _ => zeroCode)) = _
  exact decodeVectorList_aux d (Encodable.decode (α:=List ℕ) code)

theorem primitive_stateList : Primrec (fun a : ℕ × ℕ => stateList a.1 a.2) := by
  have hd : Primrec (fun a : ℕ × ℕ => decodeList a.2) := primitive_decodeList.comp Primrec.snd
  have hz : Primrec (fun a : ℕ × ℕ => List.replicate a.1 zeroCode) := by
    exact (Primrec.list_map (Primrec.list_range.comp Primrec.fst) ((Primrec.const zeroCode : Primrec (fun _ : (ℕ × ℕ) × ℕ => zeroCode)).to₂)).of_eq
      (fun a => by simp)
  exact Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp hd) Primrec.fst) hd hz

/-- A coordinate evaluator with the dimension itself as runtime natural data. -/
def coordinate (d state i : ℕ) : ℕ := (stateList d state).getD i zeroCode

theorem coordinate_eq_decode (d state i : ℕ) : coordinate d state i=
    (List.ofFn fun j : Fin d => ODECode.decodeState d state j).getD i zeroCode := by
  rw [coordinate,←decodeState_eq_list]

theorem primitive_coordinate : Primrec (fun a : ℕ × (ℕ × ℕ) => coordinate a.1 a.2.1 a.2.2) :=
  (Primrec.list_getD zeroCode).comp
    (primitive_stateList.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
    (Primrec.snd.comp Primrec.snd)

#check_explicit stateList
end SymplecticPacking.Effective.PackingStateList
