module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.Defs
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.AutRankThree.SpFourOf
import CFSG.RankThree.SubgroupLists.MitchellQuasisimple
import CFSG.RankThree.SubgroupLists.MitchellPartThreeProof
import CFSG.RankThree.SubgroupLists.SymplecticFischerSp
import CFSG.RankThree.SubgroupLists.SymplecticFischerOrth
import CFSG.RankThree.SubgroupLists.SymplecticFischerUnitary
import CFSG.RankThree.SubgroupLists.SymplecticFischerRefl
public import CFSG.Certificates.Kernel.Th.Gen.Dce
public import CFSG.Certificates.Kernel.Th.Gen.DceStruct
public import CFSG.Certificates.Kernel.Th.Gen.Fwd
public import CFSG.Certificates.Kernel.Th.Gen.Gen
public import CFSG.Certificates.Kernel.Th.Gen.Orders
public import CFSG.Certificates.Kernel.Th.Gen.Sylow2
public import CFSG.Certificates.Kernel.Th.Gen.Sylow3
public import CFSG.Certificates.Kernel.Th.Gen.Sylow5
public import CFSG.Certificates.Kernel.Th.Gen.Sylow7
public import CFSG.Certificates.Kernel.Th.S.HswTC
public import CFSG.Sporadic.Bridge.M11CheckInputs
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import CFSG.Sporadic.Th.KernelInputsBase

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open CFSG.RankThree.SubgroupLists

theorem spFourQuasisimpleThreeDvd_holds :
    SpFourQuasisimpleThreeDvd := by
  intro r _ hr2 Y hY hq
  rcases mitchell_quasisimple_sp4_of mitchellPartThree_holds fischerSpClique fischerOrthClique
    fischerSpCard fischerOrthCard fischerUnitaryCard fischerReflectionCard hr2 hY hq with
    e | e | e | e | e | ⟨-, -, ⟨e⟩⟩
  · exact Nat.card_congr e.some.toEquiv ▸ three_dvd_card_statedSp_two _
  · exact Nat.card_congr e.some.toEquiv ▸ three_dvd_card_SL_two _
  · exact Nat.card_congr e.some.toEquiv ▸ three_dvd_card_SL_two _
  · have : Fact (1 < 5) := ⟨by norm_num⟩
    exact Nat.card_congr e.some.toEquiv ▸ three_dvd_card_SL_two _
  · exact Nat.card_congr e.some.toEquiv ▸ three_dvd_card_SL_two _
  · exact three_dvd_card_of_quotient_center_alternatingGroup_seven e

end CFSG.LocalAnalysis.RankThreeUC.AGL81C
