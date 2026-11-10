module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeCharData
public import Std.Data.HashSet

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular

open CFSG.Blueprint.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.CrossChar

@[expose] def stepCode (row : Array ℕ) (c : ℕ) : ℕ :=
  (List.range 6).foldl (fun acc j => acc + row.getD (c / 256 ^ j % 256) 0 * 256 ^ j) 0

@[expose] def bfsLevel (rows : Array (Array ℕ)) (seen : Std.HashSet ℕ) (front : Array ℕ) :
    Std.HashSet ℕ × Array ℕ :=
  rows.foldl (fun (st : Std.HashSet ℕ × Array ℕ) row =>
    front.foldl (fun (st : Std.HashSet ℕ × Array ℕ) c =>
      let d := stepCode row c
      if st.1.contains d then st else (st.1.insert d, st.2.push d)) st) (seen, #[])

@[expose] def bfs (rows : Array (Array ℕ)) : ℕ → Std.HashSet ℕ → Array ℕ → Std.HashSet ℕ
  | 0, seen, _ => seen
  | n + 1, seen, front =>
    if front.isEmpty then seen else
      let r := bfsLevel rows seen front
      bfs rows n r.1 r.2

@[expose] def e6WKeys (_ : Unit := ()) : List ℕ :=
  let T := RootTables.ofCert e6Certificate
  let rows : Array (Array ℕ) := T.imgs.toArray.map List.toArray
  let id0 := encodeT (List.range Tag.E6.rank)
  let seen := bfs rows 60 (({} : Std.HashSet ℕ).insert id0) #[id0]
  (seen.toArray.qsort (· < ·)).toList

@[expose] def castL (vec : List ℕ) : List ℤ := vec.map fun x : ℕ => (x : ℤ)

@[expose] def pairZ (T : RootTables) (k : ℕ) (v : List ℤ) : ℤ := dotL (T.vecs.getD k []) v


end CFSG.LieType.SeitzGeneration.ExcWideThree.E6DiagRegular
