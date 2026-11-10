module

public import Certificates.Data.Kernel.FinModel5040.K5040
public import Certificates.Kernel.FinModel5040.Data5040

public section

namespace CertificateChecks.KernelFM5040

open CFSG.KC.LQT.P CFSG.KC.Ord CFSG.KD.A7Nat CFSG.KD.FM5040

theorem ch5040_6 : allK 10 M6 R6 S6 C6 = true := by decide +kernel

theorem ch5040_7 : allK 11 M7 R7 S7 C7 = true := by decide +kernel


end CertificateChecks.KernelFM5040

end
