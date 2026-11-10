module

public import CFSG.Milestones.ASVolI.F48.Small.Sp43ChartInputs
public import CFSG.Milestones.ASVolI.F48.Small.Sp43Base
public import Certificates.Certificate7538
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Card
public import CFSG.Quasithin.Recognition.CertOvergroup
public import CFSG.Milestones.ASVolI.F4Native
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.CharacterTheory.Semidihedral.Local.FourQuaternionAutomorphisms
public import CFSG.ClassicalGroups
public import CFSG.GH74.GLS.Bg.Statements
public import CFSG.GH74.GLS.Defs
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.AschbacherCanonicalRemaining
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ExceptionalEightPlaneCentralizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In2421Cfg4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InPartI2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellMotion
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryRootAutomorphism
public import CFSG.Permutation.BurnsideSchur
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Recognition.CertTwoLocalPair
public import CFSG.Quasithin.Recognition.CertU33Wreath
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Quasithin.Vol2.GoldschmidtF431F45Ctx
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2RootRel
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSStd
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModF4
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisNormalizers
public import CFSG.Sporadic.Schreier.J4SSylow

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42

section Words

variable {m : ℕ}


end Words

section WordLists

variable {m : ℕ} (h : Fin m → Y) (gl gli : Fin m → List ℕ)


variable {h gl gli}


end WordLists

section Model

local notation "aY" => burnsideF48s_sp43G 0
local notation "bY" => burnsideF48s_sp43G 1
local notation "pY" => burnsideF48s_sp43G 2
local notation "qY" => burnsideF48s_sp43G 3


end Model

end CFSG.ASVolI
