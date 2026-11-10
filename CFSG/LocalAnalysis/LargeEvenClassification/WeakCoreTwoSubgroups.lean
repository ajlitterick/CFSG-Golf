module

public import CFSG.LocalAnalysis.LargeEvenClassification.NormalElementary
public import CFSG.LocalAnalysis.LargeEvenClassification.InvariantKernel
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCore
public import CFSG.LocalAnalysis.LargeEvenClassification.PGroupHyperplaneGeneration

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem elementary_pRank_card {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime rank : ℕ} (hprime : 1 < prime) (Elementary : Subgroup Ambient)
    (helementary : IsElemAbelian prime Elementary) (hcard : Nat.card Elementary = prime ^ rank) :
    pRank prime Elementary = rank := by
  have hlower : rank ≤ pRank prime Elementary := by
    apply le_csSup
    · refine ⟨Nat.card Ambient, ?_⟩
      rintro otherRank ⟨OtherElementary, _, _, hotherCard⟩
      exact rank_exponent_le_card hprime OtherElementary hotherCard
    · exact ⟨Elementary, le_rfl, helementary, hcard⟩
  obtain ⟨Witness, hle, _, hwitnessCard⟩ := pRank_witness hprime Elementary
  have hcardBound := Nat.card_le_card_of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)
  rw [hwitnessCard, hcard] at hcardBound
  exact le_antisymm ((Nat.pow_le_pow_iff_right hprime).mp hcardBound) hlower

theorem elementary_hyperplane_rank_lower {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime rank : ℕ} (hprime : prime.Prime) (Elementary : Subgroup Ambient)
    (helementary : IsElemAbelian prime Elementary) (hcard : Nat.card Elementary = prime ^ rank)
    (Fixers : Subgroup Elementary) (hindex : Fixers.index ≤ prime) :
    rank ≤ pRank prime (Fixers.map Elementary.subtype) + 1 := by
  let : Fact prime.Prime := ⟨hprime⟩
  have hpgroup : IsPGroup prime Fixers := (IsPGroup.of_card hcard).to_subgroup Fixers
  obtain ⟨fixerRank, hfixerCard⟩ := hpgroup.exists_card_eq
  have hmapCard : Nat.card (Fixers.map Elementary.subtype) = prime ^ fixerRank :=
    (Nat.card_congr (Fixers.equivMapOfInjective Elementary.subtype Subtype.val_injective).toEquiv).symm.trans
      hfixerCard
  have hmapElementary : IsElemAbelian prime (Fixers.map Elementary.subtype) := by
    apply elementary_subgroup_of_le Elementary (Fixers.map Elementary.subtype) helementary
    intro element helement
    obtain ⟨source, _, rfl⟩ := helement
    exact source.property
  have hformula := Fixers.index_mul_card
  rw [hfixerCard, hcard] at hformula
  have hpower : prime ^ rank ≤ prime ^ (fixerRank + 1) := by
    rw [← hformula, pow_succ]
    exact (Nat.mul_le_mul_right (prime ^ fixerRank) hindex).trans_eq (mul_comm _ _)
  rw [elementary_pRank_card hprime.one_lt _ hmapElementary hmapCard]
  exact (Nat.pow_le_pow_iff_right hprime.one_lt).mp hpower


end CFSG.LargeEvenClassification.Helpers
