module

public import CFSG.Sporadic.SuzOddCore.GraphArraysCheck
public import CFSG.Sporadic.SuzOddCore.CertChainCheck
public import Certificates.Data.CFSGNative.Schreier.Refine
public import Mathlib.Data.Fintype.Card
public meta import CFSG.Sporadic.SuzOddCore.GraphArraysCheck
public meta import CFSG.Sporadic.SuzOddCore.CertChainCheck
public meta import Certificates.Data.CFSGNative.Schreier.Refine
public meta import Mathlib.Data.Fintype.Card

public section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def powArr (n : Nat) (t : Array Nat) : Nat → Array Nat
  | 0 => idA n
  | k + 1 => compA n t (powArr n t k)

@[expose] def zArr : Array Nat :=
  powArr 22880 (wordA 22880 certStrongArrs certStrongInvs zWord) zPower

@[expose] def deltaOf (z : Array Nat) : List Nat :=
  (List.range 22880).filter fun i => i != 0 && z[i]! == i

@[expose] def gammaNbr : Array (List Nat) :=
  adjSearch 22880 #[certArr 0, certArr 1] (deltaOf zArr)


end CFSG.Sporadic.SuzOddCore
