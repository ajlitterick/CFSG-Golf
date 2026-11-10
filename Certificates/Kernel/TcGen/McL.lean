module

public import Certificates.Data.Kernel.OpsLayMcert
public import Certificates.Kernel.LocalComp.LaySeeds
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.McLThreeData
import CFSG.Certificates.Kernel.Common.Harness
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelTc.McL 3 21
  CFSG.Blueprint.NativeSporadic.McLSeed1 CFSG.Blueprint.NativeSporadic.McLSeed2

public section

namespace CertificateChecks.KernelTc.McL

open CFSG.KC.OpsLayK CFSG.AGLEmbedding.R3 CFSG.AGLEmbedding.R3.McLThree

theorem tc_K : seedsL lay A B ⟨tcNregs, tcProg, tcSpec.facts⟩ tcSpec.rA tcSpec.rB = true := by
  quickRfl

theorem cp_K : seedsL lay A B ⟨cpNregs, cpProg, cpSpec.facts⟩ cpSpec.rA cpSpec.rB = true := by
  quickRfl


end CertificateChecks.KernelTc.McL

end
