module

public import Certificates.Data.Kernel.L34Cov.T1
public import Certificates.Kernel.L34Cov.Words
public import Certificates.Kernel.L34Cov.Checks
public import Certificates.Kernel.L34W.Tabs
public import CFSG.Certificates.Kernel.Common.EachTrue

public section

namespace CertificateChecks.KernelL34Cov

open CFSG.KC CFSG.KC.L34Cov CFSG.KC.L34W CertificateChecks.KernelL34W

#kc_each CertificateChecks.KernelL34Cov.ch22219t1c c
  (fun k => t1colsOK VT CFSG.KD.L34F4a.Tab CFSG.KD.L34F4b.Tab T1X.F TwC.codes k) 0 64

theorem t1zero_k : Mono.allR 0 64 (t1zeroOK T1X.F) = true := by decide +kernel

#kc_each CertificateChecks.KernelL34Cov.ch22219t1a a
  (fun k => Mono.allR 0 64 (t1clsOK T1X.F k)) 0 64

theorem reach_k : reachM T1X.F 5 = 2 ^ 64 - 1 := by decide +kernel


end CertificateChecks.KernelL34Cov

end
