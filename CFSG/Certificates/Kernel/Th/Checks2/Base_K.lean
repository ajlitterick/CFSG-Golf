module

public import CFSG.Certificates.Kernel.Th.S.BaseS
public import CFSG.Certificates.Kernel.Th.S.BigS
public import CFSG.Certificates.Kernel.Th.S.Data.Sm_const
public import CFSG.Certificates.Kernel.Th.S.Data.Seed_const
public import CFSG.Certificates.Kernel.Th.S.Data.Base_const
public import Certificates.Data.CFSGNative.Th.FormCheck
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Th.S.SeedS

public section

namespace CFSG.KC.Th.BaseK

open CFSG.KC.Th CFSG.KC.Th.BaseS CFSG.KD.ThS

theorem pack_C : SeedS.packOK CFSG.KD.ThBase.C deltaRows = true := by quickRfl

theorem gram : Nat.beq (mulB c rm (mulB c rm CFSG.KD.ThBase.C CFSG.KD.ThSeed.SF)
    (trB tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 CFSG.KD.ThBase.C)) CFSG.KD.ThBase.G = true := by quickRfl

theorem inv_C : Nat.beq (mulB c rm CFSG.KD.ThBase.N CFSG.KD.ThBase.C) ONE = true := by quickRfl

theorem form_base : CFSG.Sporadic.Th.formBaseCheck 124 (blkG rm CFSG.KD.ThBase.G) = true := by
  quickRfl


end CFSG.KC.Th.BaseK

end
