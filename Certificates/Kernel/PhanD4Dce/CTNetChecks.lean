module

public import Certificates.Kernel.PhanD4Dce.CTNetData
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.PhanD4CT

open CFSG.KC.MiscCoset.Act

theorem ct_let : allR (nat_lit 0) (nat_lit 1120)
    (pointOK CFSG.KAct.PhanD4CT.A (nat_lit 29) (nat_lit 1120) []) = true := by
  allR_blocks 32

theorem ct_nets : allR 0 58 (fun c => CFSG.KC.YModel.letOK 11 1120
    (lineL CFSG.KAct.PhanD4CT.A 58 c 1120) (CFSG.KAct.PhanD4CT.NT c)) = true := by
  decide +kernel

theorem ct_rels : CFSG.KC.YModel.relsOK 11 58 CFSG.KAct.PhanD4CT.NT
    (invRels (CFSG.KAct.PhanD4CT.R ++ CFSG.KAct.PhanD4CT.RD ++ CFSG.KAct.PhanD4CT.RC ++
      CFSG.KAct.PhanD4CT.RS)) = true := by
  decide +kernel

theorem ct_codes : ∀ r ∈ CFSG.KAct.PhanD4CT.R ++ CFSG.KAct.PhanD4CT.RD ++ CFSG.KAct.PhanD4CT.RC ++
    CFSG.KAct.PhanD4CT.RS, ∀ c ∈ r, c < 58 := by
  decide +kernel


end CFSG.KAct.PhanD4CT

end
