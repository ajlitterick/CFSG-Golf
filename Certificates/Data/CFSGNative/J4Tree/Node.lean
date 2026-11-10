module

public import Certificates.Data.CFSGNative.J4Tree.Index
public import Certificates.Data.CFSGNative.J4Tree.Inv
public import Std.Data.HashSet

public section

namespace CFSG.J4Tree.Native.Node

open CFSG.J4Tree.Native

set_option compiler.extract_closed false

@[expose] def bfsStep {α : Type} (gs : List α) (step : α → Code → Code) (S : Std.HashSet Code)
    (F : List Code) : Std.HashSet Code × List Code :=
  F.foldl (fun acc x => gs.foldl (fun (acc : Std.HashSet Code × List Code) g =>
    let y := step g x
    if acc.1.contains y then acc else (acc.1.insert y, y :: acc.2)) acc) (S, [])

@[expose] def bfsRun {α : Type} (gs : List α) (step : α → Code → Code) :
    Nat → Std.HashSet Code × List Code → Std.HashSet Code × List Code
  | 0, st => st
  | n + 1, st => if st.2.isEmpty then st else bfsRun gs step n (bfsStep gs step st.1 st.2)

@[expose] def bfsFrom {α : Type} (gs : List α) (step : α → Code → Code) (x₀ : Code) (n : Nat) :
    Std.HashSet Code :=
  (bfsRun gs step n ((∅ : Std.HashSet Code).insert x₀, [x₀])).1

@[expose] def closedUnder {α : Type} (gs : List α) (step : α → Code → Code)
    (S : Std.HashSet Code) : Bool :=
  S.toList.all fun x => gs.all fun g => S.contains (step g x)

@[expose] def rmul (g x : Code) : Code := x * g

@[expose] def conjP (p : Code × Code) (x : Code) : Code := p.1 * x * p.2

@[expose] def letterOf (ch : Char) : Int :=
  if ch = 'a' then 1 else if ch = 'b' then 2 else if ch = 'c' then 3
  else if ch = 'A' then -1 else if ch = 'B' then -2 else -3

@[expose] def wordOf (s : String) : List Int := s.toList.map letterOf

@[expose] def codeOfStr (s : String) : Code := codeOfWord (wordOf s)

@[expose] def cc (ce : Nat × Nat) : Code := codeOfCoord ce.1 ce.2

structure Kid where
  y : Nat × Nat
  tgt : Nat
  conj : String
deriving Inhabited


@[noinline, expose] def greedyGens (Cl : List Code) : List Code := Id.run do
  let mut gens : Array Code := #[]
  let mut cur : Std.HashSet Code := (∅ : Std.HashSet Code).insert 1
  for x in Cl do
    if !cur.contains x then
      gens := gens.push x
      cur := (bfsRun gens.toList rmul (Cl.length + 1) (cur, cur.toList)).1
  return gens.toList

@[noinline, expose] def prunedWith (S : Std.HashSet Code) (y : Code) (Cl cg : List Code) : Bool :=
  let Cc := bfsFrom cg rmul 1 (Cl.length + 1)
  let B0 := Cl.filter fun z => z * z == 1 && cg.all fun g => z * g == g * z
  cg.all (fun g => S.contains g && g * y == y * g) && Cc.contains 1 && closedUnder cg rmul Cc &&
    Cc.size == Cl.length && (decide (1024 < B0.length) || decide (64 < (B0.filter Code.inE).length))

@[noinline, expose] def prunedOK (S : Std.HashSet Code) (Sl : List Code) (y : Code) : Bool :=
  let Cl := Sl.filter fun s => s * y == y * s
  prunedWith S y Cl (greedyGens Cl)

@[noinline, expose] def mergeWith (bc : List Code) (gp : List (Code × Code)) (ordK : Nat) (y : Code)
    (tgt : Nat) (h : Code) (At O : Std.HashSet Code) : Bool :=
  let hi := h.inv
  h * hi == 1 && hi.wf && !(treeTopIds.contains tgt) && decide (1 ≤ tgt) && decide (tgt ≤ treeN) &&
    (treeBasis tgt).all (fun ce => decide (ce.2 < 1024)) && At.contains 1 &&
    closedUnder ((treeBasis tgt).map cc) rmul At &&
    (y :: bc).all (fun b => At.contains (hi * b * h)) &&
    O.contains y && closedUnder gp conjP O && O.size * treeOrd tgt == ordK

@[noinline, expose] def mergeOK (bc : List Code) (gp : List (Code × Code)) (ordK : Nat) (y : Code)
    (kd : Kid) : Bool :=
  mergeWith bc gp ordK y kd.tgt (codeOfStr kd.conj)
    (bfsFrom ((treeBasis kd.tgt).map cc) rmul 1 4096) (bfsFrom gp conjP y (ordK + 1))

@[expose] def kidOK (S : Std.HashSet Code) (Sl : List Code) (bc : List Code)
    (gp : List (Code × Code)) (ordK : Nat) (kd : Kid) : Bool :=
  decide (kd.y.2 < 1024) && S.contains (cc kd.y) && cc kd.y * cc kd.y == 1 &&
    if kd.tgt == 0 then prunedOK S Sl (cc kd.y) else mergeOK bc gp ordK (cc kd.y) kd


@[expose] def n1OK (A : Std.HashSet Code) (bc : List Code) (n : Code) : Bool :=
  n * n.inv == 1 && n.inv.wf && bc.all fun b => A.contains (n * b * n.inv)

@[expose] def normOK (A : Std.HashSet Code) (bc : List Code) (ngens : List String) : Bool :=
  ngens.all fun w =>
    n1OK A bc (codeOfStr w)


end CFSG.J4Tree.Native.Node
