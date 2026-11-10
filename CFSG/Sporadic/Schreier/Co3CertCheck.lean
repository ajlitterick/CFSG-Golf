
module

public import CFSG.Sporadic.Schreier.Co3CertCheckBase
import all CFSG.Sporadic.Schreier.Co3CertCheckBase

public import CFSG.Sporadic.Schreier.Co3Arrays
public meta import CFSG.Sporadic.Schreier.Co3Arrays
public import Certificates.Certificate2152

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3.Native

theorem co3Layout_check :
    layoutOK co3Bytes276 3 276 111 = true ∧ layoutOK co3Bytes36 2 36 83 = true ∧
    layoutOK co3Bytes12 1 12 14 = true ∧ layoutOK co3FormsBytes 1 64 276 = true ∧
    (∀ L < 111, isInvA 276 (co3Arr276 L) (invCand 276 (co3Arr276 L)) = true) ∧
    (∀ L < 83, isInvA 36 (co3Arr36 L) (invCand 36 (co3Arr36 L)) = true) ∧
    (∀ L < 14, isInvA 12 (co3Arr12 L) (invCand 12 (co3Arr12 L)) = true) ∧
    (∀ r < 276, co3FormWord r < 2 ^ 253) :=
  Certificates.certificate2152.1


end CFSG.Sporadic.Schreier.Co3
