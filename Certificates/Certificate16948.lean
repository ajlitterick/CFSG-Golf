module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThListFacts
import Certificates.Kernel.ThCent.LGlue
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2CoreDefs
public import CFSG.Perm.CentralizerOrbit
public import CFSG.Sporadic.Ly.ThreeBCount
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAutBase1

public section

namespace Certificates

open CertificateChecks

theorem certificate16948 : 
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThList.ThSevenFacts :=
  KernelThList.th_seven_facts

end Certificates
