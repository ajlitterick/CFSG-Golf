
module

public import CFSG.Sporadic.Co2Cert.Check
public import CFSG.Sporadic.Co2Rank3.CheckInputsT
import Certificates.Kernel.Sporadic.Co2R3.Final

public section

namespace Certificates

open CFSG.Sporadic.Co2Rank3 in
theorem certificate10079 :
    co2Rank3TOK = true :=
  CertificateChecks.KernelSpor.Co2R3.facts10079

end Certificates
