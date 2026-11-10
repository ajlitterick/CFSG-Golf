module

public import Certificates.Kernel.TitsOct.Checks
public import Certificates.Kernel.TitsOct.DataLam
public import Certificates.Data.Kernel.TitsOctLamK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelTitsOct

open CFSG.KC.Enum CFSG.KS CFSG.KC.TwoF4LieK CFSG.KC.TitsOctK CFSG.KC.TitsOctLamK CFSG.KD.TitsOct
  CFSG.KD.TitsOctLam


end CertificateChecks.KernelTitsOct

end
