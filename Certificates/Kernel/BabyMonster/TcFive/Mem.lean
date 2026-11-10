module

public import Certificates.Kernel.BabyMonster.RegTabTwin
public import Certificates.Kernel.BabyMonster.RegMem
public import CFSG.Certificates.Kernel.BabyMonster.TcFive.All
public import CFSG.Certificates.Kernel.BabyMonster.Five.All
public import CFSG.Certificates.Kernel.BabyMonster.FiveA.All
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check2
public import CFSG.Sporadic.Bridge.BTcData

public section

namespace CertificateChecks.KernelBM.TcFive

open CFSG.KC.BM CFSG.KC.BM.Reg CFSG.Sporadic.Bridge.B

theorem ab_mem : (∀ t ∈ [CFSG.KC.BM.TcFive.AP, CFSG.KC.BM.TcFive.BP], wfMat t = true) ∧
    MemsOK [CFSG.KC.BM.Five.f85, CFSG.KC.BM.Five.f86, CFSG.KC.BM.TcFive.E]
      [CFSG.KC.BM.TcFive.AP, CFSG.KC.BM.TcFive.BP] := by
  bm_mem_cert [CFSG.KC.BM.TcFive, CFSG.KC.BM.Five, CFSG.KC.BM.FiveA, CFSG.KC.BM.Seeds]

theorem e_mem : (∀ t ∈ [CFSG.KC.BM.TcFive.E], wfMat t = true) ∧
    MemsOK [Seeds.A1, Seeds.A2, CFSG.KC.BM.Five.Q2, CFSG.KC.BM.Five.Q3, CFSG.KC.BM.Five.Q4,
      CFSG.KC.BM.Five.Z] [CFSG.KC.BM.TcFive.E] := by
  bm_mem_cert [CFSG.KC.BM.TcFive, CFSG.KC.BM.Five, CFSG.KC.BM.FiveA, CFSG.KC.BM.Seeds]

end CertificateChecks.KernelBM.TcFive

end
