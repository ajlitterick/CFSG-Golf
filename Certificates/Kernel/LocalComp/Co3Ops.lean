module

public import Certificates.Data.Kernel.OpsF2K
public import Certificates.Data.CFSGNative.Co3.Data
meta import Certificates.Data.CFSGNative.Co3.Data
public import Certificates.Data.CFSGNative.Filter.Co3Data
public import Certificates.Data.KFCub2Co3
public import Certificates.Data.CFSGNative.MultRes.Witnesses
public import Certificates.Kernel.LocalComp.M1Gen
public import CFSG.Certificates.Kernel.LocalCompCubSound

set_option maxRecDepth 400000

public section

#ks_chars CertificateChecks.KernelLC.Co3Ops.SA CFSG.Sporadic.Co3.Native.seedA
#lc_m1 CertificateChecks.KernelLC.Co3Ops.SA CFSG.Sporadic.Co3.Native.seedA 22
#ks_chars CertificateChecks.KernelLC.Co3Ops.SB CFSG.Sporadic.Co3.Native.seedB
#lc_m1 CertificateChecks.KernelLC.Co3Ops.SB CFSG.Sporadic.Co3.Native.seedB 22

namespace CertificateChecks.KernelLC.Co3Ops

open CFSG.KC.OpsF2K CFSG.SectionRank.Native

theorem sec_K : secK 22 SA.M SB.M co3Sec = true := by decide +kernel

theorem cub2_K : cub2K 22 SA.M SB.M co3FiveData = true := by decide +kernel

theorem cub_K : CFSG.KC.LocalComp.Cub.cubicK 22 SA.M SB.M co3MultData = true := by
  decide +kernel


end CertificateChecks.KernelLC.Co3Ops

end
