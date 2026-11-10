module

import CFSG.RankThree.PartOne.S10.CentralCoverLocalRankFourObstruction
import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.RankThree.Classical.EvenSurvivingScalarRank
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.RankThree.PartTwo.Census.Criteria
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly.RankThreeEven

namespace SourceSixThirteen

theorem le_localRank_iff_exists {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) {k : ℕ}
    (hk : 1 ≤ k) :
    k ≤ localRank p G ↔ ∃ U : Subgroup G, IsPGroup 2 U ∧ U ≠ ⊥ ∧
      ∃ E : Subgroup G, E ≤ Subgroup.normalizer (U : Set G) ∧ IsElementaryAbelian p E ∧
        Nat.card E = p ^ k := by
  constructor
  · intro hle
    by_contra hno
    push Not at hno
    have hlt : localRank p G ≤ k - 1 := by
      refine csSup_le' ?_
      rintro m ⟨H', ⟨S, hS0, hS2, rfl⟩, rfl⟩
      by_contra hm
      push Not at hm
      obtain ⟨E, hEN, hE, hEc⟩ := (Planes.le_pRank_iff hp
        (Subgroup.normalizer (S : Set G)) k).1 (by omega)
      exact hno S hS2 hS0 E hEN hE hEc
    omega
  · rintro ⟨U, hU2, hU0, E, hEN, hE, hEc⟩
    have h4 : k ≤ CFSG.Assembly.pRank p (Subgroup.normalizer (U : Set G)) :=
      (Planes.le_pRank_iff hp _ k).2 ⟨E, hEN, hE, hEc⟩
    have h5 := CFSG.RankThree.Classical.pRank_le_localRank hp.one_lt
      (⟨U, hU0, hU2, rfl⟩ : CFSG.Assembly.IsTwoLocal (Subgroup.normalizer (U : Set G)))
    omega

theorem three_lt_localRank_iff_exists_elementary_abelian_normalizer {V : Type*} [Group V]
    [Finite V] {p : ℕ} (hp : p.Prime) :
    3 < localRank p V ↔ ∃ U : Subgroup V, IsPGroup 2 U ∧ U ≠ ⊥ ∧
      ∃ E : Subgroup V, E ≤ Subgroup.normalizer (U : Set V) ∧ IsElementaryAbelian p E ∧
        Nat.card E = p ^ 4 :=
  le_localRank_iff_exists hp (by norm_num)


end SourceSixThirteen

end CFSG.RankThree.PartOne
