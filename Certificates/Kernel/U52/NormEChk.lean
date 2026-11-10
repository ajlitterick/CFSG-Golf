module

public import Certificates.Kernel.U52.NormChk
public import Certificates.Kernel.U52.LettersF
public import Certificates.Kernel.U52.NormEData
public import Certificates.Data.Kernel.U52.NormE
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelU52

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KS.WordF CFSG.KS.U52N CertificateChecks.KernelU52.N
  CertificateChecks.KernelU52.NE CertificateChecks.KernelU52F


end CertificateChecks.KernelU52

end
