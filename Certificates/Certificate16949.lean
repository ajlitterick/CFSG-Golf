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

theorem certificate16949 : 
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThList.ThFiveFacts :=
  KernelThList.th_five_facts

end Certificates
