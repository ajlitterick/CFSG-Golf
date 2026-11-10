module

public import Certificates.Data.CFSGNative.SmallOddCore.Check
public import Std.Data.HashMap

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native

abbrev Word := List Int

@[expose] def commP (n : Nat) (x y : Table) : Bool := tblEq n (compT n x y) (compT n y x)

@[expose] def permP (n : Nat) (x : Table) : Bool :=
  CFSG.Monster.B.Co2.Native.isInvA n (natArr x) (CFSG.Monster.B.Co2.Native.invCand n (natArr x))

@[expose] def involP (n : Nat) (x : Table) : Bool := invoOK n x && !tblEq n x (idT n)

@[expose] def gensP (n : Nat) (gs : Array Table) : Bool :=
  gs.all fun x => permP n x && invOK n x (invT n x)

@[expose] def letterT (n : Nat) (gs gsInv : Array Table) (l : Int) : Table :=
  if 0 < l ∧ (l - 1).toNat < gs.size then gs[(l - 1).toNat]!
  else if l < 0 ∧ (-l - 1).toNat < gsInv.size then gsInv[(-l - 1).toNat]!
  else idT n

@[expose] def wordTab (n : Nat) (gs gsInv : Array Table) (w : Word) : Table :=
  wordT n (letterT n gs gsInv) w

@[expose] def commutT (n : Nat) (a b : Table) : Table :=
  compT n (compT n a b) (compT n (invT n a) (invT n b))

@[expose] def hindex (n : Nat) (L : Array Table) : Std.HashMap UInt64 Nat := Id.run do
  let mut m : Std.HashMap UInt64 Nat := {}
  for i in [0:L.size] do
    m := m.insert (hkey n L[i]!) i
  return m

@[expose] def closedHOK (n : Nat) (gens L : Array Table) : Bool :=
  let ix := hindex n L
  L.all fun x => gens.all fun g =>
    let z := compT n x g
    match ix[hkey n z]? with
    | some i => decide (i < L.size) && tblEq n L[i]! z
    | none => false

@[expose] def enumP (n cap : Nat) (gs : Array Table) (N : Nat) : Bool :=
  let e := mulClosureH n gs cap
  gensP n gs && mulTreeOK n gs e.1 e.2.1 e.2.2 && closedHOK n (gs ++ gs.map (invT n)) e.1 &&
    hkeysDistinct n e.1.toList && e.1.size == N


structure JWords where
  a₁ : Word
  b₁ : Word
  a₂ : Word
  b₂ : Word

@[expose] def jEls (n : Nat) (gs gi : Array Table) (jw : JWords) : Array Table :=
  #[wordTab n gs gi jw.a₁, wordTab n gs gi jw.b₁, wordTab n gs gi jw.a₂, wordTab n gs gi jw.b₂]

@[expose] def jGens (n : Nat) (gs gi : Array Table) (jw : JWords) : Array Table :=
  let e := jEls n gs gi jw
  #[commutT n e[0]! e[1]!, commutT n e[2]! e[3]!]

@[expose] def wordsLE (m : Nat) (w : Word) : Bool := w.all fun l => l != 0 && decide (l.natAbs ≤ m)

structure G5Row where
  z : Word
  k : Word
  wa : Word
  wb : Word

structure DData where
  gens : Array Table
  x : Word
  jw : JWords
  rB : Word
  g5 : List G5Row


@[expose] def commClosedOK (n : Nat) (E JL : Array Table) : Bool :=
  E.all fun a => invOK n a (invT n a) && E.all fun b => memT n JL (commutT n a b)


structure RData where
  gens : List Word
  order : Nat
  perf : List (List (Word × Word))

structure RepData where
  rep : Word
  rdata : Option RData

structure KData where
  gens : Array Table
  x : Word
  jw : JWords
  reps : List RepData


@[expose] def jNormalOK (n : Nat) (HL JL : Array Table) : Bool :=
  HL.all fun h =>
    let hi := invT n h
    invOK n h hi && JL.all fun j => memT n JL (conjT n h hi j)


end CFSG.EvenSporadicStandard.M12Std.PropA.Native
