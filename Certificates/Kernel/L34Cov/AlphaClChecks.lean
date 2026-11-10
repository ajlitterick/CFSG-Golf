module

public import Certificates.Data.Kernel.L34Cov.AlphaCl
public import Certificates.Kernel.L34Cov.Words
public import Certificates.Kernel.L34Cov.Checks
public import Certificates.Kernel.L34W.Tabs
public import CFSG.Certificates.Kernel.Common.EachTrue

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.KC.L34W CertificateChecks.KernelL34W

#kc_each CertificateChecks.KernelL34Cov.ch22219acl a
  (fun i => alClOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab T1X.F FW AlX.F
    (UAC.codes.getD i []) (UBC.codes.getD i []) i) 0 36


end CertificateChecks.KernelL34Cov

end
