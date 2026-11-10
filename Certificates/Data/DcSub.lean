module

public import Certificates.Data.DcRows

public section

namespace CFSG.Quasithin.H13.LocDbl.DcNative


@[expose] def subEnumOK (n : Nat) (B : List Nat) (N cap : Nat) (Yt : Array (Array Nat)) : Bool :=
  let e := bfsEnumL n B Yt cap
  enumOK N Yt e.1 e.2 && distinctNat (rowKeys n B Yt e.1 e.2 N) && closedOK n B Yt e.1 e.2 N &&
    decide (0 < N)


end CFSG.Quasithin.H13.LocDbl.DcNative
