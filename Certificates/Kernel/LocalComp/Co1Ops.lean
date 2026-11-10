module

public import Certificates.Data.Kernel.OpsF2KSq
public import Certificates.Data.CFSGNative.Co1.Data
meta import Certificates.Data.CFSGNative.Co1.Data
public import Certificates.Data.CFSGNative.Filter.Co1Data
public import Certificates.Data.CFSGNative.MultRes.Witnesses
public import Certificates.Kernel.LocalComp.M1Gen

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelLC.Co1Ops.SA CFSG.Sporadic.Co1.Native.seedA
#lc_m1 CertificateChecks.KernelLC.Co1Ops.SA CFSG.Sporadic.Co1.Native.seedA 24
#ks_chars CertificateChecks.KernelLC.Co1Ops.SB CFSG.Sporadic.Co1.Native.seedB
#lc_m1 CertificateChecks.KernelLC.Co1Ops.SB CFSG.Sporadic.Co1.Native.seedB 24

namespace CertificateChecks.KernelLC.Co1Ops

open CFSG.KC.OpsF2K CFSG.SectionRank.Native

theorem sec_K : secK 24 SA.M SB.M co1Sec = true := by decide +kernel

theorem sq_K : sqK 24 SA.M SB.M co1MultData = true := by decide +kernel


end CertificateChecks.KernelLC.Co1Ops

end
