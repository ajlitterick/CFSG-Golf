module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerSpectrum
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestriction

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u


theorem signalizerGenerated_restriction_map_eq {G : Type u} [Group G]
    (actor overgroup : Subgroup G) (signalizer : G → Subgroup G) (hactorLe : actor ≤ overgroup) :
    (signalizerGenerated (actor.subgroupOf overgroup) (restrictedSignalizer overgroup signalizer)).map
      overgroup.subtype =
        ⨆ (element : G) (_ : element ∈ actor) (_ : element ≠ 1), signalizer element ⊓ overgroup := by
  simp only [signalizerGenerated, Subgroup.map_iSup, restrictedSignalizer_map_eq]
  apply le_antisymm
  · apply iSup_le
    intro element
    apply iSup_le
    intro hmem
    apply iSup_le
    intro hne
    exact le_iSup_of_le (element : G) (le_iSup_of_le hmem
      (le_iSup_of_le (fun heq => hne (Subtype.ext heq)) le_rfl))
  · apply iSup_le
    intro element
    apply iSup_le
    intro hmem
    apply iSup_le
    intro hne
    exact le_iSup_of_le (⟨element, hactorLe hmem⟩ : overgroup) (le_iSup_of_le hmem
      (le_iSup_of_le (fun heq => hne (congrArg Subtype.val heq)) le_rfl))


theorem SignalizerComplete.restriction {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor overgroup : Subgroup G) (signalizer : G → Subgroup G)
    (hactorLe : actor ≤ overgroup)
    (hsignalizer : IsSolvableSignalizerFunctor prime actor signalizer)
    (hcomplete : SignalizerComplete prime actor signalizer) :
    SignalizerComplete prime (actor.subgroupOf overgroup) (restrictedSignalizer overgroup signalizer) := by
  apply (signalizer_compatible_restriction_iff prime actor overgroup signalizer hactorLe _).mpr
  apply SignalizerCompatible.of_le prime actor signalizer (signalizerGenerated actor signalizer) _ hcomplete
  · rw [signalizerGenerated_restriction_map_eq actor overgroup signalizer hactorLe]
    apply iSup_le
    intro element
    apply iSup_le
    intro hmem
    apply iSup_le
    intro hne
    exact inf_le_left.trans (signalizer_value_le_generated actor signalizer element hmem hne)
  · have hrestricted := restrictedSignalizer_isSolvableSignalizerFunctor prime hprime
      actor overgroup signalizer hsignalizer
    have hnormalized := signalizerGenerated_normalized prime (actor.subgroupOf overgroup)
      (restrictedSignalizer overgroup signalizer) hrestricted
    apply Subgroup.le_normalizer_iff.mpr
    intro member hmember element helement
    obtain ⟨preimage, hpreimage, rfl⟩ := helement
    exact Subgroup.mem_map_of_mem overgroup.subtype
      (Subgroup.le_normalizer_iff.mp hnormalized ⟨member, hactorLe hmember⟩ hmember preimage hpreimage)

end CFSG.RankThreeEvenClassification.Helpers
