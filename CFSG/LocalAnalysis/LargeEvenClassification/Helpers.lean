module

public import CFSG.Mathlib.GroupTheory.Basic
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.Open.LocalVocabulary

public section

open CFSG.Open

namespace CFSG.LargeEvenClassification.Helpers

universe groupUniverse

theorem rank_exponent_le_card {Ambient : Type groupUniverse} [Group Ambient]
    [Finite Ambient] {prime exponent : ℕ} (hprime : 1 < prime)
    (Elementary : Subgroup Ambient) (hcard : Nat.card Elementary = prime ^ exponent) :
    exponent ≤ Nat.card Ambient := by
  exact le_trans (Nat.le_of_lt (Nat.lt_pow_self hprime))
    (hcard ▸ Elementary.card_le_card_group)

theorem pRank_le_card {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : 1 < prime) (Local : Subgroup Ambient) :
    pRank prime Local ≤ Nat.card Ambient := CFSG.SectionRank.pRank_le_card_of_one_lt hprime Local

theorem pRank_witness {Ambient : Type groupUniverse} [Group Ambient] [Finite Ambient]
    {prime : ℕ} (hprime : 1 < prime) (Local : Subgroup Ambient) :
    ∃ Elementary : Subgroup Ambient,
      Elementary ≤ Local ∧ IsElemAbelian prime Elementary ∧
        Nat.card Elementary = prime ^ pRank prime Local :=
  CFSG.SectionRank.exists_pRank hprime Local


theorem not_isPGroup_of_nonabelian_simple (Ambient : Type groupUniverse) [Group Ambient]
    [Finite Ambient] [IsSimpleGroup Ambient] {prime : ℕ} (hprime : prime.Prime)
    (hnonab : ∃ first second : Ambient, first * second ≠ second * first) :
    ¬ IsPGroup prime Ambient := by
  intro hpgroup
  let : Fact prime.Prime := ⟨hprime⟩
  let : Group.IsNilpotent Ambient := hpgroup.isNilpotent
  let : CommGroup Ambient := instCommGroupOfIsSimpleGroupOfIsNilpotent
  obtain ⟨first, second, hne⟩ := hnonab
  exact hne (mul_comm first second)

theorem twoLocal_ne_top (Ambient : Type groupUniverse) [Group Ambient] [Finite Ambient]
    [IsSimpleGroup Ambient]
    (hnonab : ∃ first second : Ambient, first * second ≠ second * first)
    (Local : Subgroup Ambient) (hlocal : IsTwoLocal Local) : Local ≠ ⊤ := by
  obtain ⟨TwoSubgroup, hnontrivial, hpgroup, hnormalizer⟩ := hlocal
  intro htop
  have hnormal : TwoSubgroup.Normal := Subgroup.normalizer_eq_top_iff.mp
    (hnormalizer.symm.trans htop)
  rcases CFSG.eq_bot_or_eq_top_of_normal TwoSubgroup hnormal with hbot | hwhole
  · exact hnontrivial hbot
  · have hpambient : IsPGroup 2 Ambient := by
      rw [hwhole] at hpgroup
      exact hpgroup.of_equiv Subgroup.topEquiv
    exact not_isPGroup_of_nonabelian_simple Ambient Nat.prime_two hnonab hpambient


end CFSG.LargeEvenClassification.Helpers
