module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Kernel.LocalComp.LaySeeds
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenG23Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenO73Data
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanWeakGenU43Data
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelTc.G23 3 14
  CFSG.AGLEmbedding.R3.G23Three.seedA CFSG.AGLEmbedding.R3.G23Three.seedB

#lay_seeds CertificateChecks.KernelTc.O73 3 7
  CFSG.AGLEmbedding.R3.O73Three.seedA CFSG.AGLEmbedding.R3.O73Three.seedB

#lay_seeds CertificateChecks.KernelTc.U43 3 8
  CFSG.AGLEmbedding.R3.U43Three.seedA CFSG.AGLEmbedding.R3.U43Three.seedB

public section

namespace CertificateChecks.KernelTc

open CFSG.KC.OpsLayK CFSG.AGLEmbedding.R3

theorem G23.cp_K : seedsL G23.lay G23.A G23.B ⟨G23Three.nregs, G23Three.cpProg,
    G23Three.cpSpec.facts⟩ G23Three.cpSpec.rA G23Three.cpSpec.rB = true := by
  quickRfl

theorem O73.cp_K : seedsL O73.lay O73.A O73.B ⟨O73Three.nregs, O73Three.cpProg,
    O73Three.cpSpec.facts⟩ O73Three.cpSpec.rA O73Three.cpSpec.rB = true := by
  quickRfl

theorem U43.cp_K : seedsL U43.lay U43.A U43.B ⟨U43Three.nregs, U43Three.cpProg,
    U43Three.cpSpec.facts⟩ U43Three.cpSpec.rA U43Three.cpSpec.rB = true := by
  quickRfl


end CertificateChecks.KernelTc

end
