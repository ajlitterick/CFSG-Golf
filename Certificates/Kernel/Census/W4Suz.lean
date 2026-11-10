module

public import Certificates.Data.Kernel.OpsW4N
public import Certificates.Data.RankThree46Odd.Suz
public import Certificates.Kernel.LocalComp.F3.Suz

set_option maxRecDepth 400000

public section

namespace CertificateChecks.KernelCensus.W4Suz

open CFSG.KC.OpsW4N CFSG.RankThree.PartTwo.Census CFSG.SectionRank.Native

theorem suz_K : w4L CFSG.KD.LC.F3.Suz.lay CFSG.KD.LC.F3.Suz.A CFSG.KD.LC.F3.Suz.B suzW3.base
    suzW3.inv = true := by decide +kernel


end CertificateChecks.KernelCensus.W4Suz

end
