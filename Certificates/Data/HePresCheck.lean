module

public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.He.Certificate
public import CFSG.Certificates.CosetTableCompactColumns
public import Certificates.Data.HePresData
public import CFSG.Certificates.CosetTableShort
public import Mathlib

public section

namespace CFSG.ComponentClassification.AS81.HePres.Native

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.CosetTable

@[expose] def letterArrW {k : Nat} (gens invs : Array (Array Nat)) (l : Fin k × Bool) :
    Array Nat :=
  if l.2 then gens.getD l.1.val #[] else invs.getD l.1.val #[]

@[expose] def wordArrW {k : Nat} (n : Nat) (gens invs : Array (Array Nat))
    (w : List (Fin k × Bool)) : Array Nat :=
  w.foldr (fun l acc => compA n (letterArrW gens invs l) acc) (idA n)

@[expose] def relArrCheck {k : Nat} (n : Nat) (gens invs : Array (Array Nat))
    (rels : List (List (Fin k × Bool))) : Bool :=
  rels.all fun r => eqA n (wordArrW n gens invs r) (idA n)

@[expose] def modelCheck {k : Nat} (n : Nat) (gens : Array (Array Nat))
    (rels : List (List (Fin k × Bool))) : Bool :=
  let invs := gens.map (invCand n)
  (List.range k).all (fun i => isInvA n (gens.getD i #[]) (invs.getD i #[])) &&
    relArrCheck n gens invs rels


@[expose] def heT1Letters : List Int := [1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2]


abbrev hePiRelsH₁ := restrictWords (subsetOf _ [0, 1, 2, 3, 4, 6, 7]) hePiRels

abbrev hePiRelsH₂ := restrictWords (subsetOf _ [0, 1, 2, 3, 4]) hePiRelsH₁

abbrev hePiRelsH₃ := restrictWords (subsetOf _ [0, 1, 2, 3]) hePiRelsH₂

end CFSG.ComponentClassification.AS81.HePres.Native
