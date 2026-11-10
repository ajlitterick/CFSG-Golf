module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ActionPlaneTransport
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerLocalCompletion

public section

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

set_option maxHeartbeats 700000 in
theorem coprime_centralizer_generation_of_plane {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor subgroup : Subgroup G)
    (hpower : ∀ member : actor, member ^ prime = 1) (hcard : Nat.card actor = prime ^ 2)
    (hcomplement : ¬prime ∣ Nat.card subgroup)
    (hnormalized : actor ≤ Subgroup.normalizer (subgroup : Set G)) :
    subgroup = ⨆ (member : actor) (_ : member ≠ 1),
      subgroup ⊓ Subgroup.centralizer ({(member : G)} : Set G) := by
  let generated : Subgroup G := ⨆ (member : actor) (_ : member ≠ 1),
    subgroup ⊓ Subgroup.centralizer ({(member : G)} : Set G)
  have hgeneratedLe : generated ≤ subgroup := iSup_le fun _ => iSup_le fun _ => inf_le_left
  have htop : generated.subgroupOf subgroup = ⊤ := by
    apply subgroup_eq_top_of_contains_sylows
    intro sylowPrime hsylowPrime
    have : Fact sylowPrime.Prime := ⟨hsylowPrime⟩
    obtain ⟨sylow, hsylowNormalized⟩ := exists_normalized_sylow_in_prime_complement_subgroup
      prime hprime actor subgroup (IsPGroup.of_card hcard) hcomplement hnormalized sylowPrime hsylowPrime
    let ambient := (sylow : Subgroup subgroup).map subgroup.subtype
    have hambientGroup : IsPGroup sylowPrime ambient := sylow.isPGroup'.map subgroup.subtype
    have : Group.IsNilpotent ambient := hambientGroup.isNilpotent
    have hambientLe : ambient ≤ subgroup := Subgroup.map_subtype_le _
    have hambientComplement : ¬prime ∣ Nat.card ambient :=
      fun hdivides => hcomplement (hdivides.trans (Subgroup.card_dvd_of_le hambientLe))
    have hambientGenerated : ambient ≤ generated := by
      rw [solvable_centralizer_generation_of_plane prime hprime actor ambient hpower hcard
        inferInstance hambientComplement hsylowNormalized]
      apply iSup_le
      intro member
      apply iSup_le
      intro hne
      exact le_iSup_of_le member (le_iSup_of_le hne (inf_le_inf hambientLe le_rfl))
    exact ⟨sylow, fun member hmember => hambientGenerated (Subgroup.mem_map_of_mem subgroup.subtype hmember)⟩
  exact le_antisymm ((Subgroup.subgroupOf_eq_top.mp htop)) hgeneratedLe


end CFSG.RankThreeEvenClassification.Helpers
