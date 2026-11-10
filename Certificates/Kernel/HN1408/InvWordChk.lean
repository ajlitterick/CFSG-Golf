module

public import Certificates.Kernel.HN1408.InvWordDefs
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.HN1408.CzTDefs

public section

set_option maxRecDepth 400000

namespace CFSG.KD.HN1408.CzInv

open CFSG.EvenSporadicStandard.HNRecog

theorem azWords_ok : azWordsK = true := by quickRfl

theorem bWords_ok : bWordsK = true := by quickRfl


end CFSG.KD.HN1408.CzInv

end
