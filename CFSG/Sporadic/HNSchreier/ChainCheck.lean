module

public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import Certificates.Certificate2096

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native

theorem card_J_cert :
    Nat.card (CFSG.Sporadic.F5.J hnsData) = 273030912000000 :=
  Certificates.certificate2096


end CFSG.Sporadic.HNSchreier.Native
