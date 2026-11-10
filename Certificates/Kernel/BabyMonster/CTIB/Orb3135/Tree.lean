module

public import Certificates.Kernel.BabyMonster.CTIB.Orb3135Data
public import Certificates.Kernel.LocalComp.BlockTac
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelBM.CTIB.Orb3135

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.KC.BM.OrbW CFSG.KD.Orb3135

theorem inc : ∀ i < 30240, incB 1008 30240 8388608 SB i = true := by lc_cover 5040

theorem tree : ∀ i < 30240, treeB act 15 1008 30240 0 SB TB i = true := by lc_cover 1008

theorem root : Nat.beq (ptB 1008 SB 0) 854 = true := by quickRfl


end CertificateChecks.KernelBM.CTIB.Orb3135

end
