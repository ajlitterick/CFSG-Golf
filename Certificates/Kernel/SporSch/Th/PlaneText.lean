module

public import Certificates.Kernel.SporSch.Th.Cent
public import Certificates.Kernel.SporSch.Th.GenV4
public import CFSG.Sporadic.ThSchreier.PlaneChainDataInputs
public import CFSG.Sporadic.ThSchreier.PlaneSepDataInputs
meta import CFSG.Sporadic.ThSchreier.PlaneSepDataInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#kss_strof CertificateChecks.KernelSporSch.ThCSR CFSG.Sporadic.ThSchreier.chainSmallRows
#kss_strof CertificateChecks.KernelSporSch.ThCP0 CFSG.Sporadic.ThSchreier.chainPerm0
#kss_strof CertificateChecks.KernelSporSch.ThCP1 CFSG.Sporadic.ThSchreier.chainPerm1
#kss_strof CertificateChecks.KernelSporSch.ThSF CFSG.Sporadic.ThSchreier.sepFNats
#kss_strof CertificateChecks.KernelSporSch.ThSW CFSG.Sporadic.ThSchreier.sepWords
#kss_strof CertificateChecks.KernelSporSch.ThSR CFSG.Sporadic.ThSchreier.sepRowNats

namespace CertificateChecks.KernelSporSch.ThPlane

open CFSG.KS.SporSch CFSG.Sporadic.ThSchreier CertificateChecks.KernelSporSch
open CertificateChecks.KernelSporSch.ThCent

meta def swFlat : List Nat := sepWords.flatMap fun w => w.length :: w.map Int.toNat

#kss_natlist CertificateChecks.KernelSporSch.ThPlane.SWN swFlat


end CertificateChecks.KernelSporSch.ThPlane

end
