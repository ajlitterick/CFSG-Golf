module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableKFacts
import Certificates.Kernel.HN1408.TableKAsm
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Iso
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Walter.JRFacts

public section

namespace Certificates

open CFSG.EvenSporadicStandard.HNRecog in
theorem certificate26773 : Nat.card ↥P1408 = 177408000 → TableKFacts :=
  CFSG.KD.HN1408.TK.tableKFacts

end Certificates
