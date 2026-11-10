module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvolutionCountIdentities
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionInvolutionCountTwoCycles

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount

open CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerTripleTransport
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

variable {G Ω : Type*} [Group G] [MulAction Gᵐᵒᵖ Ω]

abbrev fullFlipSet (u : G) (a b : Ω) : Set G :=
  {v | v ∈ fullClass u ∧ rightAct a v = b}

def classFlipPairSetEquiv (u : G) (a b : Ω) :
    classFlipPair u a b ≃ fullFlipSet u a b where
  toFun v := ⟨v.val.val, v.val.property, v.property⟩
  invFun v := ⟨⟨v.val, v.property.1⟩, v.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl


end CFSG.ProperTwoGeneratedCore.LocalCriterionInvolutionCount
