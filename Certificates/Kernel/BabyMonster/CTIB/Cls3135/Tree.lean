module

public import Certificates.Kernel.BabyMonster.CTIB.Cls3135Data
public import Certificates.Kernel.LocalComp.BlockTac

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelBM.CTIB.Cls3135

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.KC.BM.OrbW CFSG.KD.Cls3135

theorem inc : ∀ i < 34560, incB 960 34560 8388608 DB i = true := by lc_cover 5760

theorem tree : ∀ i < 34560, treeB fact 37 960 34560 0 DB UB i = true := by lc_cover 960

theorem root : Nat.beq (ptB 960 DB 0) 43 = true := by quickRfl

theorem target : Nat.beq (ptB 960 DB 61) 10875 = true := by quickRfl


end CertificateChecks.KernelBM.CTIB.Cls3135

end
