module

public import CFSG.Milestones.ASVolI.H1
import CFSG.Quasithin.AppendixH.H11.Quadratic
import CFSG.Quasithin.AppendixH.H11.TwoRank
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.Recognition.GoldschmidtTripleQuotient
public import CFSG.Quasithin.Recognition.M12AmalAutClass
public import Certificates.Kernel.HMathieu.C7075
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.ClassicalGroups
import CFSG.Dihedral.FourgroupCycleControl
import CFSG.Dihedral.OriginalCentralizerOddCore
import CFSG.LieType.Ree.LargeReeEightTorus
import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57SL
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
import CFSG.Permutation.AlternatingAutomorphism
import CFSG.Quasithin.Background.A3Structure36A
import CFSG.Quasithin.Background.A3Structure36BBase
import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
import CFSG.Quasithin.Background.F9G2
import CFSG.Quasithin.Background.F9Geometry
import CFSG.Quasithin.Background.G9Stmts
import CFSG.Quasithin.Background.GoldschmidtAutM12Orders
import CFSG.Quasithin.Background.GoldschmidtAutM12Transfer
import CFSG.Quasithin.Background.GoldschmidtZ2D8Sylow
import CFSG.Quasithin.Background.HTriSolv
import CFSG.Quasithin.Background.HTriU3
import CFSG.Quasithin.Background.InternalSecB51
import CFSG.Quasithin.Background.InternalSecFF
import CFSG.Quasithin.Vol2.Ch10SecA1012Three
import CFSG.Quasithin.Vol2.Ch10SecA1012Two
import CFSG.Quasithin.Vol2.Ch10StatementsE
import CFSG.Quasithin.Vol2.Ch11SecA02Card
import CFSG.Quasithin.Vol2.Ch11SecAFacts02
import CFSG.Quasithin.Vol2.Ch11StatementsB
import CFSG.Quasithin.Vol2.Ch11StatementsC
import CFSG.Quasithin.Vol2.Ch1Faithful
import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
import CFSG.RankThree.Asc83Table.PermTables
import CFSG.Sporadic.Schreier.M11
import CFSG.Sporadic.Schreier.TitsOther
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.Walter.J1

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

@[expose] noncomputable def m12Model : FFModel where
  Gam := ↥CFSG.Blueprint.NativeSporadic.M12
  Amb := G6.PermMod 12
  act g x := G6.permAct 12 (g : Equiv.Perm (Fin 12)) x
  sec := G6.coreMod 12
  ker := Subgroup.zpowers (G6.allOnes 12)

end CFSG.ASVolI.ChH

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.ASVolI.ChH

@[expose] def H_11_1 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V] [Finite (MulAut V)], (∀ v : V, v ^ 2 = 1) →
  ∀ M : Subgroup (MulAut V), m12Model.Realizes (perfectCore M) ⊤ ⊥ →
    ((M ≠ perfectCore M → CFSG.Open.pRank 2 M = 4) ∧ (M = perfectCore M → CFSG.Open.pRank 2 M = 3)) ∧
    E3.mParam M = 4 ∧
    ¬ H.IsFOneModule M ∧
    (∀ A : Subgroup (MulAut V), A ≤ M → IsElemAbelian2 A → Nat.card A = 16 →
      Nonempty (↥M ≃* MulAut ↥CFSG.Blueprint.NativeSporadic.M12) ∧ rk ↥(fixV A) ≤ 3 ∧
        8 ≤ rk ↥(xiSub A)) ∧
    (∀ A : Subgroup (MulAut V), A ≤ M → ¬ IsCyclic ↥A → IsQuadratic A →
      (∀ a ∈ A, a ≠ 1 → IsTwoCentralElt M a) ∨ (rk ↥A = 2 ∧ 4 < rkIdx (fixV A)))

section H11Proof

open CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M12
  CFSG.Quasithin.AppendixH.H11


end H11Proof

end CFSG.ASVolI
