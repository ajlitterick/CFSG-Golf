module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalComponentObstruction
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SubnormalPrimeCores

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers

theorem trivial_primeComplementCore_center_le_pCore
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (hcore : primeComplementCore (G := G) prime = ⊥) :
    Subgroup.center G ≤ pCore prime G := by
  have hnilpotent : Group.IsNilpotent (Subgroup.center G) := by
    apply Subgroup.isNilpotent_of_lowerCentralSeries_eq_bot (n := 1)
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
    exact Subgroup.commutator_self_eq_bot_iff.mpr inferInstance
  have hpGroup := normal_nilpotent_isPGroup_of_primeComplementCore_eq_bot prime hprime hcore
    (Subgroup.center G) inferInstance hnilpotent
  exact normal_pGroup_le_pCore prime (Subgroup.center G) inferInstance hpGroup


end CFSG.RankThreeCoreUniqueness.Helpers
