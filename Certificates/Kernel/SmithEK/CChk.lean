module

public import Certificates.Data.Kernel.SmithEKC
public import Certificates.Kernel.SmithEK.Cols
public import Certificates.Kernel.UnitarySix.Tables

public section

namespace CertificateChecks.KernelSmithEK

open CFSG.SmithE.K

theorem c21260conj : chkCF cs.L CertificateChecks.KernelU6.T.R = true := by
  decide +kernel


end CertificateChecks.KernelSmithEK
