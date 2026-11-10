module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2Step
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8G2LeviA2

public section

namespace CFSG.ComponentClassification.RankTwoExceptional

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AS76b
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ProperTwoGeneratedCore.LocalCriterionClassFreeAffineHull
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoClassical (Sec3)
open CFSG.Blueprint.Chevalley CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.ComponentClassification.RankTwoStandard

theorem step814_g2_model
    (h4 : Asc75Theorem4) (h32 : Lemma32) (h33 : Lemma33Three) : Step814 .G2 :=
  step814_g2 h4 h32 h33 g2Centr184 g2Centr184s g2Levi187 g2TorusConj

variable {G : Type} [Group G] [Finite G]

end CFSG.ComponentClassification.RankTwoExceptional
