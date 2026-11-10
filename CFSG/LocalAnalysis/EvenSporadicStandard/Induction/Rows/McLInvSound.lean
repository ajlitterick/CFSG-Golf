module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.McLInvData
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.AutBoundSylow
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourEnumSpec
public import CFSG.Sporadic.McL
import Certificates.Kernel.Sporadic.OddCore.McL27214D
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Sporadic.ON.Gen
import Certificates.Kernel.Sporadic.OddCore.PEnumGlue
import Certificates.Kernel.CosPresTab.JWGlue
import CFSG.Certificates.Kernel.L34KSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.L34KSnd.Tab
import Certificates.Kernel.Sporadic.OddCore.McL27214OD
import CFSG.Certificates.Kernel.BfsPinSetSound
import Certificates.Kernel.Sporadic.OddCore.McL27214CD
import CFSG.Certificates.Kernel.HeAutKSound

public section

namespace CFSG.EvenSporadicStandard.McLInv

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.Th
  CFSG.Sporadic.McL CFSG.EvenSporadicStandard.Induction.AutBound

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

end CFSG.EvenSporadicStandard.McLInv
