module

public import CFSG.Sporadic.Schreier.RuCheckOrbLBInputs
public import CFSG.Sporadic.Schreier.RuWitArrays
public import Certificates.Data.CFSGNative.SporadicSchreier.Classes
public meta import CFSG.Sporadic.Schreier.RuCheckOrbLBInputs
public meta import CFSG.Sporadic.Schreier.RuWitArrays
public meta import Certificates.Data.CFSGNative.SporadicSchreier.Classes

public section

namespace CFSG.EvenSporadicStandard.TwoRu.HypOne

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.Sporadic.RuSchreier


@[expose] def tblOfArr (t : Array ℕ) : Table := t.map UInt32.ofNat

@[expose] def letterTab (gens gensInv : Array Table) (z : ℤ) : Table :=
  if 0 < z then gens[z.toNat - 1]! else gensInv[(-z).toNat - 1]!

@[expose] def cGens : Array Table := #[tblOfArr ruC0A, tblOfArr ruC1A]

@[expose] def cGensInv : Array Table := #[tblOfArr (ruInv ruC0A), tblOfArr (ruInv ruC1A)]

@[expose] def lGens : Array Table := ruLGensA.map tblOfArr

@[expose] def lGensInv : Array Table := (ruLGensA.map ruInv).map tblOfArr


end CFSG.EvenSporadicStandard.TwoRu.HypOne
