module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.MaximalElementary
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CatalogSimpleFactors
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CentralComponentLifts

public section

open CFSG.Open
open CFSG.Open

namespace CFSG.RankThreeCoreUniqueness.Helpers


theorem quasisimple_subgroup_not_le_pCore
    {G : Type*} [Group G] [Finite G] (prime : ℕ) (hprime : prime.Prime)
    (quasisimpleGroup : Subgroup G) (hquasisimple : IsQuasisimple quasisimpleGroup) :
    ¬ quasisimpleGroup ≤ pCore prime G := by
  let : Fact prime.Prime := ⟨hprime⟩
  let : Group.IsPerfect quasisimpleGroup := Group.isPerfect_def.mpr hquasisimple.1
  let : IsSimpleGroup (quasisimpleGroup ⧸ Subgroup.center quasisimpleGroup) := hquasisimple.2
  let : Nontrivial quasisimpleGroup :=
    (QuotientGroup.mk'_surjective (Subgroup.center quasisimpleGroup)).nontrivial
  intro hbound
  exact Group.IsPerfect.not_isNilpotent quasisimpleGroup
    ((pCore_isPGroup prime).to_le hbound).isNilpotent


end CFSG.RankThreeCoreUniqueness.Helpers
