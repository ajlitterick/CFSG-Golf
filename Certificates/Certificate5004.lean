module

public meta import Mathlib
public import CFSG.GH74.E2.Alpha1AutCertInputs
import CFSG.Certificates.Kernel.SD16Code
meta import CFSG.Certificates.Kernel.Common.Harness

open CFSG.GH74.E2 CFSG.Semidihedral CFSG.KS.SD16Code

namespace CertificateChecks.Batch5004

open CFSG.GH74.E2 CFSG.Semidihedral CFSG.KS.SD16Code

local instance instDecEqSD16MFor5004 : DecidableEq SD16M := inferInstance

end CertificateChecks.Batch5004

