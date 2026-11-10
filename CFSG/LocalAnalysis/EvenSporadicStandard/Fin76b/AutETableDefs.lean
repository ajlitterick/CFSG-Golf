module

public import Mathlib.Data.Nat.Notation

public section

namespace CFSG.EvenSporadicStandard.Fin76b.AutETable

@[expose] def tab (n : ℕ) (f : ℕ → ℕ) : Array ℕ := (Array.range n).map f

@[expose] def tab2 (n : ℕ) (mul : ℕ → ℕ → ℕ) : Array (Array ℕ) :=
  (Array.range n).map fun a => tab n (mul a)

@[expose] def mt (M : Array (Array ℕ)) (a b : ℕ) : ℕ := (M.getD a #[]).getD b 0

@[expose] def ix (A : Array ℕ) (k : ℕ) : ℕ := A.getD k 0

@[expose] def wd (W : Array (List ℕ)) (k : ℕ) : List ℕ := W.getD k []

@[expose] def ev (M : Array (Array ℕ)) (g : ℕ → ℕ) (w : List ℕ) : ℕ :=
  w.foldl (fun acc i => mt M acc (g i)) 0

@[expose] def inLv (W : Array (List ℕ)) (d k : ℕ) : Bool := (wd W k).all fun i => decide (i ≤ d)

@[expose] def count (R : Array (Option (List ℕ))) : ℕ :=
  R.foldl (fun c o => if o.isSome then c + 1 else c) 0

@[expose] def closePass (n : ℕ) (M : Array (Array ℕ)) (gens : List ℕ)
    (R : Array (Option (List ℕ))) : Array (Option (List ℕ)) :=
  (List.range n).foldl (fun R k =>
    match R.getD k none with
    | none => R
    | some w => (List.range gens.length).foldl (fun R i =>
        let m := mt M k (gens.getD i 0)
        match R.getD m none with
        | none => R.setIfInBounds m (some (w ++ [i]))
        | some _ => R) R) R

@[expose] def closeFuel (n : ℕ) (M : Array (Array ℕ)) (gens : List ℕ) :
    ℕ → Array (Option (List ℕ)) → Array (Option (List ℕ))
  | 0, R => R
  | f + 1, R =>
    let R' := closePass n M gens R
    if count R' == count R then R else closeFuel n M gens f R'

@[expose] def pickGen (n : ℕ) (M : Array (Array ℕ)) (gens : List ℕ)
    (R : Array (Option (List ℕ))) : Option ℕ :=
  let cands := (List.range n).filter fun k => (R.getD k none).isNone
  let best := cands.foldl (fun (best : Option (ℕ × ℕ)) k =>
    let c := count (closeFuel n M (gens ++ [k]) n R)
    match best with
    | none => some (k, c)
    | some (_, bc) => if bc < c then some (k, c) else best) none
  best.map Prod.fst

@[expose] def mkGens (n : ℕ) (M : Array (Array ℕ)) : List ℕ × Array (Option (List ℕ)) :=
  (List.range n).foldl (fun (st : List ℕ × Array (Option (List ℕ))) _ =>
    match pickGen n M st.1 st.2 with
    | none => st
    | some k => (st.1 ++ [k], closeFuel n M (st.1 ++ [k]) n st.2))
    ([], (Array.replicate n (none : Option (List ℕ))).setIfInBounds 0 (some []))


end CFSG.EvenSporadicStandard.Fin76b.AutETable
