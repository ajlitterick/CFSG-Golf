module

public meta import CFSG.Sporadic.ThSchreier.Text
public import Certificates.Certificate2319

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

@[expose] def sepFRows : Array V4 := Array.ofFn (n := 248) fun i => v4OfNat (sepFNats.getD i.val 0)


@[expose] def sepCRows : Array V4 :=
  Array.ofFn (n := 248) fun j => v4OfNat (sepRowNats.getD j.val 0)


end CFSG.Sporadic.ThSchreier
