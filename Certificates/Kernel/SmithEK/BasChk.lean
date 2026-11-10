module

public import Certificates.Data.Kernel.SmithEKI
public import Certificates.Kernel.SmithEK.Bas
public import Certificates.Kernel.SmithEK.Pts
public import Certificates.Kernel.SmithEK.Tab

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem bs_ok : basOK cT.L pts.L bs.L = true := by
  decide +kernel


end CertificateChecks.KernelSmithEK
