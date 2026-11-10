module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.TableICheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.TwoHSData.Words
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface
import Certificates.Kernel.HN1408.TableIShape
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.S9Iso
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Walter.JRFacts

public section

namespace Certificates

open CFSG.EvenSporadicStandard.HNRecog in
theorem certificate26772 : tableI1OK = true ∧ tableI3OK = true ∧
    (Nat.card ↥(Subgroup.closure (elemW '' {w | w ∈ blkData2.gens})) = 80640 →
      Subgroup.closure (elemW '' {w | w ∈ blkData2.gens}) =
        P1408 ⊓ Subgroup.centralizer ({elemB} : Set (Equiv.Perm (Fin 1408))) →
      IsShapeTwoTwoTimesA8 ↥(Subgroup.closure (elemW '' {w | w ∈ blkData2.gens}))) :=
  ⟨CFSG.KD.HN1408.tI1, CFSG.KD.HN1408.tI3, CFSG.KD.HN1408.tableI2_shape_of⟩

end Certificates
