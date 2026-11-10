module

public import Certificates.Kernel.SectionRankHS.Seeds
public import Certificates.Data.Kernel.OpsF2KQ
public import Certificates.Data.CFSGNative.Filter.HSData

public section

namespace CertificateChecks.KernelSRHS

open CFSG.KC.OpsF2K CFSG.SectionRank.Native

theorem sec_Q : secQ 20 SA.M SB.M hsSec = true := by decide +kernel


end CertificateChecks.KernelSRHS
