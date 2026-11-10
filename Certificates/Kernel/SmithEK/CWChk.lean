module

public import Certificates.Data.Kernel.SmithEKCW
public import Certificates.Data.Kernel.SmithEKW
public import Certificates.Kernel.SmithEK.Cols
public import Certificates.Kernel.SmithEK.WData
meta import Certificates.Kernel.SmithEK.GenCW

#kc_eval CertificateChecks.KernelSmithEK cw CertificateChecks.KernelSmithEK.cwStep

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem cw_ok : cwK (wBits wd.W) cw.E cs.L = true := by
  decide +kernel


end CertificateChecks.KernelSmithEK
