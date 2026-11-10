module

public import Certificates.Data.CFSGNative.Th.Data
public import Certificates.Data.CFSGNative.Th.Sift
public import Certificates.Data.CFSGNative.Th.Suborbits

public section

set_option compiler.extract_closed false

namespace CFSG.Sporadic.Th.Native

@[expose] def tblA (_ : Unit) : Array V4 := frTable (transposeRows (rowsOf seedA))

@[expose] def tblB (_ : Unit) : Array V4 := frTable (transposeRows (rowsOf seedB))

@[expose] def thBFS (_ : Unit) : BFSState :=
  let st := bfs (tblA ()) (tblB ()) wKey 150000000
  ⟨id st.keys, id st.slots, id st.alpha, id st.beta, id st.par, id st.count⟩

@[expose] def thN (_ : Unit := ()) : Nat := 143127000

@[expose] def q0Size (_ : Unit := ()) : Nat := 11741184

@[expose] def q1Size (_ : Unit := ()) : Nat := 54

@[expose] def suborbitSizes (_ : Unit := ()) : List Nat :=
  [1, 11741184, 5031936, 105670656, 8805888, 8128512, 1304576, 45864, 2201472, 179712, 17199]

@[expose] def deltaOK (st : BFSState) : Bool :=
  allIn 0 124 fun i => (readKey st.keys i).beq (deltaKeys[i]!)

@[inline, expose] def letters (P₁ P₂ : Table) (s : Nat) : Table := if s = 1 then P₁ else P₂

@[inline, expose] def wordLetters (P Q Qi : Table) (l : Int) : Table :=
  if l = 1 ∨ l = -1 then P else if l = 2 then Q else Qi

@[expose] def abPow19 (α β : Table) (p : Nat) : Nat :=
  (List.range 19).foldl (fun q _ => ap α (ap β q)) p

@[expose] def globalChecks (n : Nat) (alpha beta betaInv gpl : Table) (c : Chain) (chunks : Nat) :
    Bool :=
  parAll n chunks (fun i =>
      (!reqTwo gpl (ap alpha) 1 i ||
        globalTest gpl (letters alpha beta) (letters alpha betaInv) c 1 i) &&
      (!reqThree gpl (ap beta) 2 i ||
        globalTest gpl (letters alpha beta) (letters alpha betaInv) c 2 i)) &&
    parAll n chunks (fun i => abPow19 alpha beta i == i)


end CFSG.Sporadic.Th.Native
