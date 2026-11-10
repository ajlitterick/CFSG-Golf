module

public import Certificates.Kernel.BabyMonster.RegTabTwin
public import CFSG.Certificates.Kernel.BabyMonster.Three.All
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2

public section

namespace CertificateChecks.KernelBM.Three

open CFSG.KC.BM CFSG.KC.BM.Reg CFSG.Monster.B.Primes.Native

theorem three_regs : RegsOK threeProg [(1, some Seeds.A1), (2, some Seeds.A2)] true [1, 2]
    [CFSG.KC.BM.Three.t79, CFSG.KC.BM.Three.t58] := by
  bm_reg_cert_twin [CFSG.KC.BM.Three, CFSG.KC.BM.Seeds]

end CertificateChecks.KernelBM.Three

end
