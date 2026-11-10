module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexRecognitionParameter
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOddInvolutions

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII

universe u v

theorem identity_adjoined_whole_involution_card
    {L : Type u} [Group L] [Finite L] (P : Subgroup L) :
    Nat.card ↥(({1} : Set L) ∪ {x : L | x ∈ P ∧ IsInvolution x}) =
      Nat.card {x : L // x ∈ P ∧ IsInvolution x} + 1 := by
  classical
  let I : Set L := {x : L | x ∈ P ∧ IsInvolution x}
  have hone : (1 : L) ∉ I := by
    intro h
    exact h.2.ne_one rfl
  change Nat.card ↥(({1} : Set L) ∪ I) = Nat.card I + 1
  rw [Set.singleton_union, Nat.card_congr (Equiv.Set.insert hone), Nat.card_sum]
  rw [Nat.card_unique (α := PUnit.{u + 1})]


end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
