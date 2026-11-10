module

public import CFSG.LocalAnalysis.ComponentClassification.PComponentCentralizers
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction

public section

namespace CFSG.ComponentClassification.CatalogueBPrimeJoin

open CFSG CFSG.LocalCores

variable {G : Type*} [Group G] [Finite G]

theorem pComponent_ne_bot {p : ℕ} [Fact p.Prime] {L : Subgroup G} (hL : IsPComponent p L) :
    L ≠ ⊥ := by
  rintro rfl
  apply core_ne_top p ⊥ hL
  have : Subsingleton (⊥ : Subgroup G) := inferInstance
  exact Subsingleton.elim _ _


end CFSG.ComponentClassification.CatalogueBPrimeJoin
