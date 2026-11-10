module

public import Certificates.Data.Kernel.SmithEKP
public import Certificates.Kernel.SmithEK.Cols

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem pchk_ok : chkPF pts.L cs.L = true := by
  decide +kernel


end CertificateChecks.KernelSmithEK
