module

public import Certificates.Data.CFSGNative.Timmesfeld.ThCent
public import Certificates.Data.CFSGNative.SectionRank.Elem3
public meta import Certificates.Data.CFSGNative.Timmesfeld.ThCent
public meta import Certificates.Data.CFSGNative.SectionRank.Elem3

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative

open CFSG.Sporadic.Th.Native CFSG.SectionRank.Native

set_option compiler.extract_closed false

@[expose] def opRows (R : Array (Array V4)) : Op → Array (Array V4)
  | .mul i j k => R.setIfInBounds k (mulRows R[i]! R[j]!)
  | .pow e i k => R.setIfInBounds k (powRowsN R[i]! e)

@[expose] def initRows (A B : Array V4) (n : Nat) : Array (Array V4) :=
  Array.ofFn (n := n) fun r => if r.val = 0 then A else if r.val = 1 then B else idRows

@[expose] def slpRows (A B : Array V4) (n : Nat) (prog : List Op) : Array (Array V4) :=
  prog.foldl opRows (initRows A B n)

@[expose] def wordRowsL (gs : Array (Array V4)) (w : List Nat) : Array V4 :=
  w.foldl (fun acc r => mulRows acc gs[r]!) idRows

@[expose] def rowAt (X : Array V4) (k : Nat) : V4 := X[k]?.getD V4.zero

@[expose] def rowsDiffer (X Y : Array V4) : Bool :=
  (List.range 248).any fun k => (List.range 248).any fun c =>
    (rowAt X k).testBit c != (rowAt Y k).testBit c

@[expose] def pairOK (X Y : Array V4) (p : Nat) : Bool :=
  eqRows (powRowsN X p) idRows && eqRows (powRowsN Y p) idRows &&
    eqRows (mulRows X Y) (mulRows Y X) && rowsDiffer X idRows &&
    (List.range p).all fun k => rowsDiffer Y (powRowsN X k)

@[expose] def conjOK (regs : Array (Array V4)) (X Y Z : Array V4) (p : Nat)
    (W : Array (List Nat)) : Bool :=
  (List.range p).all fun a => (List.range p).all fun b => a + b == 0 ||
    ((W[p * a + b]!).all (fun r => decide (r < regs.size)) &&
      let M := wordRowsL regs W[p * a + b]!
      eqRows (mulRows M (mulRows (powRowsN X a) (powRowsN Y b))) (mulRows Z M))


structure CoreList where
  n : Nat
  m : Nat
  row : Nat
  words : Array (List Nat)
  inv : Array Nat
  wit : Array (List Nat)


end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThSlpNative
