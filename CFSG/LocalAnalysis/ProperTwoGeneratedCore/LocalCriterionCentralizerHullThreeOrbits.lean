module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullOrbits
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCentralizerHullPartition

public noncomputable section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull

open CFSG.BenderSuzuki CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry

universe u v

theorem entire_three_orbit_quotient
    {A : Type u} [Group A] {X : Type v} [MulAction A X]
    (a b c : X)
    (hcover : ∀ x : X, x ∈ MulAction.orbit A a ∨
      x ∈ MulAction.orbit A b ∨ x ∈ MulAction.orbit A c)
    (hab : MulAction.orbit A a ≠ MulAction.orbit A b)
    (hac : MulAction.orbit A a ≠ MulAction.orbit A c)
    (hbc : MulAction.orbit A b ≠ MulAction.orbit A c) :
    Set.range (MulAction.orbitRel.Quotient.orbit :
      MulAction.orbitRel.Quotient A X → Set X) =
        {MulAction.orbit A a, MulAction.orbit A b, MulAction.orbit A c} ∧
      Nat.card (MulAction.orbitRel.Quotient A X) = 3 := by
  have hrange : Set.range (MulAction.orbitRel.Quotient.orbit :
      MulAction.orbitRel.Quotient A X → Set X) =
        {MulAction.orbit A a, MulAction.orbit A b, MulAction.orbit A c} := by
    ext s
    constructor
    · rintro ⟨q, rfl⟩
      induction q using Quotient.inductionOn'
      rename_i x
      rw [MulAction.orbitRel.Quotient.orbit_mk]
      rcases hcover x with hx | hx | hx
      · exact Or.inl (MulAction.orbit_eq_iff.mpr hx)
      · exact Or.inr (Or.inl (MulAction.orbit_eq_iff.mpr hx))
      · exact Or.inr (Or.inr (MulAction.orbit_eq_iff.mpr hx))
    · rintro (hs | hs | hs)
      · exact ⟨Quotient.mk'' a, by simpa only [MulAction.orbitRel.Quotient.orbit_mk] using hs.symm⟩
      · exact ⟨Quotient.mk'' b, by simpa only [MulAction.orbitRel.Quotient.orbit_mk] using hs.symm⟩
      · exact ⟨Quotient.mk'' c, by simpa only [MulAction.orbitRel.Quotient.orbit_mk] using hs.symm⟩
  refine ⟨hrange, ?_⟩
  rw [← Set.ncard_range_of_injective MulAction.orbitRel.Quotient.orbit_injective, hrange]
  have hnot : MulAction.orbit A a ∉
      ({MulAction.orbit A b, MulAction.orbit A c} : Set (Set X)) := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using And.intro hab hac
  rw [Set.ncard_insert_of_notMem hnot, Set.ncard_pair hbc]


end CFSG.ProperTwoGeneratedCore.LocalCriterionCentralizerHull
