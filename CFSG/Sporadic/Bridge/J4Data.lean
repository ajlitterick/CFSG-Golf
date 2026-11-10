module

public import Certificates.Data.CFSGNative.J4.Cert
public import Certificates.Data.CFSGNative.Bridge.SurjD

public section

namespace CFSG.Sporadic.Bridge.J4.Native

open CFSG.Sporadic.J4.Native CFSG.Sporadic.Bridge.SurjD.Native

set_option compiler.extract_closed false

@[expose] def letterOfZ (l : Nat × Bool) : Int :=
  if l.2 then (l.1 : Int) + 1 else -((l.1 : Int) + 1)

@[expose] def imgText : String := include_str "J4Images.txt"


@[expose] def imgWords : List (List Int) := (parseWords imgText).toList


end CFSG.Sporadic.Bridge.J4.Native
