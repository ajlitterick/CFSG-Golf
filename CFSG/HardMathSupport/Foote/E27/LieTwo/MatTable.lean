module

public import CFSG.HardMathSupport.Foote.E27.TableSylow
public import CFSG.HardMathSupport.Foote.E27.TableMat

public section

namespace CFSG.HardMathSupport.Foote.E27

open Matrix CFSG.Sporadic.He.Native

abbrev M2 (d : ℕ) : Type := Matrix (Fin d) (Fin d) (ZMod 2)

abbrev AM : Type := Array (Array ℕ)

structure RawTab where
  elts : Array AM
  par : Array (ℕ × ℕ)
  L : Array (Array ℕ)

@[expose] def buildTab (d : ℕ) (gens : Array AM) (fuel : ℕ) : RawTab :=
  let m := gens.size
  let init : RawTab := ⟨#[idM d], #[(0, 0)], Array.replicate m #[]⟩
  let step : RawTab → ℕ → RawTab := fun st i =>
    (List.range m).foldl (fun (st : RawTab) j =>
      let p := mulM 2 d gens[j]! st.elts[i]!
      match st.elts.findIdx? (matEqB 2 d p) with
      | some k => { st with L := st.L.modify j (·.push k) }
      | none => ⟨st.elts.push p, st.par.push (i, j), st.L.modify j (·.push st.elts.size)⟩) st
  (List.range fuel).foldl (fun st i => if i < st.elts.size then step st i else st) init

@[expose] def tabOK (d : ℕ) (gens : Array AM) (T : RawTab) : Bool :=
  let n := T.elts.size
  (T.par.size == n) && matEqB 2 d T.elts[0]! (idM d) &&
  (List.range n).all (fun i => (i == 0) ||
    (decide ((T.par[i]!).1 < i) && decide ((T.par[i]!).2 < gens.size) &&
      matEqB 2 d T.elts[i]! (mulM 2 d gens[(T.par[i]!).2]! T.elts[(T.par[i]!).1]!))) &&
  (List.range gens.size).all (fun j => (List.range n).all fun i =>
    decide ((T.L[j]!)[i]! < n) &&
      matEqB 2 d (mulM 2 d gens[j]! T.elts[i]!) T.elts[(T.L[j]!)[i]!]!) &&
  (List.range n).all (fun i => (List.range i).all fun k => !(matEqB 2 d T.elts[i]! T.elts[k]!))

section Spec


end Spec

end CFSG.HardMathSupport.Foote.E27
