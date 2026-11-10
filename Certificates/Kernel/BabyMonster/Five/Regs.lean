module

public import Certificates.Kernel.BabyMonster.RegTabTwin
public import CFSG.Certificates.Kernel.BabyMonster.Five.All
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2

public section

namespace CertificateChecks.KernelBM.Five

open CFSG.KC.BM CFSG.KC.BM.Reg CFSG.Monster.B.Primes.Native

theorem five_regs : RegsOK fiveProg [(1, some Seeds.A1), (2, some Seeds.A2)] true [1, 2]
    [CFSG.KC.BM.Five.f85, CFSG.KC.BM.Five.f86] := by
  bm_reg_cert_twin [CFSG.KC.BM.Five, CFSG.KC.BM.Seeds]

end CertificateChecks.KernelBM.Five

end
