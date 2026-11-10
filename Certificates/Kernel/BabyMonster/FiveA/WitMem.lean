module

public import Certificates.Kernel.BabyMonster.RegMem
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.All
public import CFSG.Certificates.Kernel.BabyMonster.Five.All
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2

public section

namespace CertificateChecks.KernelBM.FiveA

open CFSG.KC.BM CFSG.KC.BM.Reg

theorem wit_mem : (∀ t ∈ [FiveA.v40, FiveA.v177, FiveA.v178, FiveA.v179], wfMat t = true) ∧
    MemsOK [Seeds.A1, Seeds.A2, Five.Q2, Five.Q3, Five.Q4, Five.Z]
      [FiveA.v40, FiveA.v177, FiveA.v178, FiveA.v179] := by
  bm_mem_cert [CFSG.KC.BM.FiveA, CFSG.KC.BM.Five, CFSG.KC.BM.Seeds]

end CertificateChecks.KernelBM.FiveA

end
