module

public import Certificates.Data.CFSGNative.Co1.CoTwoChain

public section

namespace CFSG.Sporadic.Co1.CoTwoAutNative

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Co1.OddNative CFSG.Sporadic.Co1.CoTwoNative
  CFSG.Sporadic.SmallF2.Native


@[expose] def maskOf (m : Nat) (l : List Nat) : Array Bool :=
  l.foldl (fun a j => a.set! j true) (Array.replicate m false)


end CFSG.Sporadic.Co1.CoTwoAutNative
