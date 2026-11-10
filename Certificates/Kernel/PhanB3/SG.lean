module

public import Certificates.Kernel.PhanB3.SGData
public import Certificates.Kernel.PhanB3.CTData
public import Certificates.Kernel.Misc.Coset.ActBlocks
import CFSG.Certificates.Kernel.Common.Harness

set_option maxRecDepth 100000

public section

namespace CFSG.KAct.PhanB3SG

open CFSG.KC.MiscCoset.Act

theorem rows : allR (nat_lit 0) (nat_lit 1120) (fun x =>
    rowsOK CFSG.KAct.PhanB3CT.A (nat_lit 28) CFSG.KAct.PhanB3SG.B (nat_lit 19)
      CFSG.KAct.PhanB3SG.EW x (nat_lit 0)) = true := by
  allR_blocks 32

theorem levels : levelsOK CFSG.KAct.PhanB3SG.B (nat_lit 19) (nat_lit 1120) CFSG.KAct.PhanB3SG.LV
    [] = true := by
  decide +kernel


end CFSG.KAct.PhanB3SG

end
