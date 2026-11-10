module

public import Certificates.Kernel.HN1408.RepWitDefs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CzInv

theorem rep_wit_ok : repWitK = true := by quickRfl


end CFSG.KD.HN1408.CzInv

end
