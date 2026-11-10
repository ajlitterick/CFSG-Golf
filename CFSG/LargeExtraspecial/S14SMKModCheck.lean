module

public import CFSG.LargeExtraspecial.SMod20BasicCheck

public section

namespace CFSG.SmithE

open CFSG.F4.Native

@[expose] def vecSyn (fs : Array Nat) (y : Nat) : Nat :=
  (List.range fs.size).foldl (fun acc s => if fB fs[s]! y then acc ||| 2 ^ s else acc) 0

@[expose] def vecSynEchelon (fs : Array Nat) : List (Nat × Nat) :=
  (List.range 20).foldl
    (fun E m => insertVec E (vecSyn fs (2 ^ m) ||| 2 ^ (m + fs.size))) []

@[expose] def vecDual (fs : Array Nat) : Array Nat :=
  let E := vecSynEchelon fs
  Array.ofFn (n := fs.size) fun t =>
    ((E.find? fun be => be.1 == t.val).map fun be => be.2 >>> fs.size).getD 0


@[expose] def tvDiff (p c : Nat) : Nat := applyCols tvArr[p]! c ^^^ c

@[expose] def qaStep (i : Nat) (st : List (Nat × Nat) × Array (Nat × Nat)) (p k : Nat) :
    List (Nat × Nat) × Array (Nat × Nat) :=
  if st.2.size == 10 then st else
    if oppB i k then st else
      let v := tvDiff p wtArr[k]!
      if reduceBy st.1 v == 0 then st else (insertVec st.1 v, st.2.push (p, k))

@[expose] def qaGens (i : Nat) : Array (Nat × Nat) :=
  (planePtsArr[i]!.foldl (fun st p => (List.range 891).foldl (fun st k => qaStep i st p k) st)
    (([] : List (Nat × Nat)), (#[] : Array (Nat × Nat)))).2

@[expose] def qaVecs (i : Nat) : Array Nat := (qaGens i).map fun pk => tvDiff pk.1 wtArr[pk.2]!


@[expose] def cvStep (st : List (Nat × Nat) × Array (Nat × Nat)) (p m : Nat) :
    List (Nat × Nat) × Array (Nat × Nat) :=
  if st.2.size == 19 then st else
    let v := tvDiff p (2 ^ m)
    if reduceBy st.1 v == 0 then st else (insertVec st.1 v, st.2.push (p, m))

@[expose] def cvGens (i : Nat) : Array (Nat × Nat) :=
  (planePtsArr[i]!.foldl (fun st p => (List.range 20).foldl (fun st m => cvStep st p m) st)
    (([] : List (Nat × Nat)), (#[] : Array (Nat × Nat)))).2

@[expose] def cvVecs (i : Nat) : Array Nat := (cvGens i).map fun pm => tvDiff pm.1 (2 ^ pm.2)


end CFSG.SmithE
