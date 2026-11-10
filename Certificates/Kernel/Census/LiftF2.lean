module

public import Certificates.Data.Kernel.OpsV4
public import Certificates.Data.TripleCoverLift.Co3
public import Certificates.Data.TripleCoverLift.Co2
public import Certificates.Data.TripleCoverLift.Th
public import Certificates.Kernel.AlphaMc.SeedsF2
public import Certificates.Kernel.LocalComp.ThOrder
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCensus.LiftF2

open CFSG.KC.OpsV4 CFSG.KC.OpsK CFSG.RankThree.PartTwo.Sec4.Census CFSG.SectionRank.Native

theorem co3_K : liftN (opsF2K 22) KernelAM.C3A.M KernelAM.C3B.M co3Lift = true := by quickRfl

theorem co2_K : liftN (opsF2K 22) KernelAM.C2A.M KernelAM.C2B.M co2Lift = true := by quickRfl

theorem th_K : liftN (opsF2K 248) KernelLC.ThA.M KernelLC.ThB.M thLift = true := by quickRfl


end CertificateChecks.KernelCensus.LiftF2

end
