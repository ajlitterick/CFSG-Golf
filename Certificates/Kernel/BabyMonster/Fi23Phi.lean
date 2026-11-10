module

public import Certificates.Kernel.BabyMonster.Fi23Fu
public import Certificates.Kernel.Sporadic.Fi23Fu.Rels
import Certificates.Kernel.Sporadic.Fi23Br.Checks
import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.BabyMonster.Fi23Phi.All

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelBM.Fi23Phi

open CFSG.KC.BM CFSG.Sporadic.GLQ CertificateChecks.KernelBM.Fi23InB CertificateChecks.KernelBM.Fi23Fu CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

local notation "sm" => stripMat

end CertificateChecks.KernelBM.Fi23Phi

end
