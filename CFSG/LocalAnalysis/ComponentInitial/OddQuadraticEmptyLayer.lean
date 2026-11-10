module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverage
public import CFSG.LocalAnalysis.ComponentInitial.QuadraticLowDimension
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitComponents
public import CFSG.GroupTheory.LocalCores.Layer

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.ComponentClassification

theorem not_isComponent_of_isSolvable {G : Type*} [Group G] [Group.IsSolvable G]
    (L : Subgroup G) : ¬ CFSG.IsComponent L := by
  intro hL
  have := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
  have := hL.1.1
  exact Group.IsPerfect.not_isSolvable L
    (Group.isSolvable_of_isSolvable_injective L.subtype_injective)

theorem isComponent_of_le_of_normal {G : Type*} [Group G] {L N : Subgroup G} [N.Normal]
    (hq : CFSG.IsQuasisimple L) (hLN : L ≤ N) (hn : (L.subgroupOf N).Normal) :
    CFSG.IsComponent L :=
  ⟨hq, Subgroup.IsSubnormal.step L N hLN (Subgroup.Normal.isSubnormal inferInstance) hn⟩


end CFSG.LocalAnalysis.ComponentInitial
