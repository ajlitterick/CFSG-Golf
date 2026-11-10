module

public import Certificates.Data.CFSGNative.PSL3Four.Basic

public section

namespace CFSG.Certificates.PermutationCatalogue.Data

open CFSG.PSL3Four.Native

structure Transition where
  representative : Nat
  conjugator : Nat
  target : Nat
  words : Array (Array (Option Nat))
deriving Inhabited

structure Cover where
  transition : Nat
  left : Nat
  right : Nat
deriving Inhabited

structure Row where
  gens : Array Nat
  elems : Enum
  transitions : Array Transition
  cover : Array Cover
deriving Inhabited

structure Input where
  ambient : Enum
  ambientInv : Array Tab
  rows : Array Row
  bottom : Nat
deriving Inhabited


end CFSG.Certificates.PermutationCatalogue.Data
