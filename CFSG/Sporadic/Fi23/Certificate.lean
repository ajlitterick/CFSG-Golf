
module

public import CFSG.Sporadic.Fi23.CertificateBase
import all CFSG.Sporadic.Fi23.CertificateBase

public meta import Certificates.Data.CFSGNative.Fi23.Certificate
public import Certificates.Certificate1012

public section

namespace CFSG.Sporadic.Fi23

open Native

theorem fi23_certificate : fi23Certificate 3 = true :=
  Certificates.certificate1012

end CFSG.Sporadic.Fi23
