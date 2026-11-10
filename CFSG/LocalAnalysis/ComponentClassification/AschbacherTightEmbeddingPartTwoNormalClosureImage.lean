module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoOddQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoPreimage

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.ProperTwoGeneratedCore

variable {G K : Type*} [Group G] [Group K]

theorem normal_closure_map (f : G →* K) (hf : Function.Surjective f)
    (Q : Subgroup G) :
    (Subgroup.normalClosure (Q : Set G)).map f =
      Subgroup.normalClosure (Q.map f : Set K) := by
  rw [Subgroup.map_normalClosure _ f hf, Subgroup.coe_map]


end CFSG.ComponentClassification.AschbacherTightEmbedding
