module

public import Certificates.Data.CFSGNative.D42Over.Basic

public section

namespace CFSG.D42Over.Native

set_option compiler.extract_closed false


structure ClassData where
  kW : List Nat
  s0 : List (List Nat)
  roots : List (List Nat)
  gens : List (List Int × List Int)
  n : Nat


@[expose] def ClassData.k (c : ClassData) : NMat := nWord c.kW

@[expose] def ClassData.S (c : ClassData) : Array NMat := (c.s0.map nWord).toArray


end CFSG.D42Over.Native
