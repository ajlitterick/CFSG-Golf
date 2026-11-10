module

public import CFSG.Quasithin.Vol2.Ch10Reselect.Wire10A
public import CFSG.Quasithin.H13.NQBlockRadicalR2Frontier
public import CFSG.Quasithin.H13.NQBlockStmt1317Ten
public import CFSG.LocalAnalysis.SteinbergCCExistingCLS
public import CFSG.Quasithin.H13.NQCoreCh1Statements
public import CFSG.Quasithin.H13.NQCoreP134
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.RankThree.OddKernel.SporadicKernelCases
public import CFSG.RankThree.PartOne.S10.CoprimeTransitiveSemisimpleSectionOrbit
public import CFSG.RankThree.PartOne.S10.CyclicSemisimpleSectionOrbit
public import CFSG.RankThree.PartTwo.Late.GammaZero
public import CFSG.RankThree.PartTwo.Sec13.Statements
public import CFSG.RankThree.PartTwo.Sec18.Notation
public import CFSG.RankThree.PartTwo.Sec18.Transport
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors
public import CFSG.Sporadic.Bridge.BOrder
public import CFSG.Sporadic.Bridge.BSurjInputs
public import CFSG.Sporadic.Th.CertificateBase
public import CFSG.Sporadic.Th.CertificateBase1
public import CFSG.Sporadic.ThSchreier.KernelAut
public import CFSG.Sporadic.ThSchreier.KernelAutBase1

public section

namespace CFSG.Quasithin.H13.NQBlock

open CFSG.Open CFSG.QuasithinUnique

theorem stmt13_1_7_of_frontierA
    (h1323 : Stmt13_1_2_three) (hIn : Vol2.Ch10.Inputs10_0_1A) (h701 : Stmt7_0_1) :
    Stmt13_1_7 :=
  have h1001 : Stmt10_0_1 := Vol2.Ch10.stmt10_0_1_of_remainingA hIn
  stmt13_1_7_of_as317 h1323 h1001
    (stmt3_2_14_of_frontier
      (Vol2.Ch10.stmtFSUChoice_of_a36 stmt3_2_3_proved VolI.a36ForSQTK_holds) h701
      Vol2.Ch10.a312ListFactsCat_holds Ch3T316W.theorem316Statement_holds)
    as317Sylow_proved

end CFSG.Quasithin.H13.NQBlock

end
