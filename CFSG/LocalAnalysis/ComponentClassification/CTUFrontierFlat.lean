module

public import CFSG.LocalAnalysis.ComponentClassification.KProperComponentLocalBLeavesHarris
import Certificates.Kernel.LocalComp.L34T3.Glue
public import CFSG.LocalAnalysis.ComponentClassification.CTUSimpleRecognition
public import CFSG.LocalAnalysis.ComponentClassification.KProperComponentLocalBLeavesFlat
public import CFSG.LocalAnalysis.ComponentClassification.CTUSol76HbOddLieLeaves
public import CFSG.GH74.GLS.Prop27.FromSUKInputs
public import CFSG.GH74.KGroups.KI5b
public import CFSG.GH74.QTGen4.DSGen4.Leaf.L34ParabA
public import CFSG.GH74.Uniqueness.SU.KI1r3Final
public import CFSG.GH74.Uniqueness.SU.SU10P211
public import CFSG.LieType.Chevalley.CLSEvenTrialityFourGroup
public import CFSG.LieType.SteinbergBRLieModelRankOneClassifier
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherEvenRankOneSmallModels
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticEvenAllInvolutionFourGroup
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinRed
public import CFSG.RankThree.PartTwo.Sec11.Theorem1134
public import CFSG.RankThree.PartTwo.Sec21.Hering214KHS
public import CFSG.RankThree.PartTwo.Sec21.Item21Early3ProofExists

public section

namespace CFSG.ComponentClassification.CTUSimple

open CFSG

section Certified

theorem ctu_kproper_simple_unbalanced_recognition_models_of_flatLeavesGS
    (hGH : UFrontier.GH74ModelsInput) (hCI : GSLit.ClassicalInvolutionInput)
    (hb : Sol76.Lemma315bInputFor Sol76T13.simpleAmbient) (hL : KProperRelativeB.FlatBundleGS)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (z : G) (hz : orderOf z = 2)
    (hunbal : CFSG.oddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥) :
    (CFSG.Blueprint.OddLieType G ∨
      ∃ n : ℕ, 7 ≤ n ∧ n % 4 = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∧
      CFSG.Blueprint.Catalog G :=
  ctu_kproper_simple_unbalanced_recognition_models_of_inputs
    (UFrontier.relativeU_of_tripleBranch FooteLit.catalogAlmostSimpleUnbalancedOutcome_holds
      UFrontier.lowTwoRankCatalogInput
      (fun G _ _ _ hnonab S hrank hcore =>
        CFSG.Milestones.cl_lit_aschbacher_proper_two_generated_core G hnonab S hrank hcore)
      hGH
      (KProperRelativeB.tripleBranch_of_flatBundleGS hGH hCI hb hL))
    G hnonab hK z hz hunbal

theorem ctu_kproper_simple_unbalanced_recognition_models_of_flatK2LeavesGS
    (hGH : UFrontier.GH74ModelsInput) (hCI : GSLit.ClassicalInvolutionInput)
    (h39 : Sol76.Sig.Lemma39TwoDiscK2At Sol76.Sig.solRestrictedHub)
    (hSJ : Sol76.Sig.QuasisimpleSylowFourJoinedSCN)
    (hQSi : Sol76.Sig.SolomonQTwoDisconnectedSylowInvFor)
    (hL : KProperRelativeB.FlatBundleGS)
    (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G)
    (z : G) (hz : orderOf z = 2)
    (hunbal : CFSG.oddCore (Subgroup.centralizer ({z} : Set G)) ≠ ⊥) :
    (CFSG.Blueprint.OddLieType G ∨
      ∃ n : ℕ, 7 ≤ n ∧ n % 4 = 3 ∧ Nonempty (G ≃* alternatingGroup (Fin n))) ∧
      CFSG.Blueprint.Catalog G :=
  ctu_kproper_simple_unbalanced_recognition_models_of_flatLeavesGS hGH hCI
    (Sol76.Sig.lemma315bInputFor_simple_of_hbK2Leaves h39 hSJ hQSi)
    hL G hnonab hK z hz hunbal

end Certified

end CFSG.ComponentClassification.CTUSimple
