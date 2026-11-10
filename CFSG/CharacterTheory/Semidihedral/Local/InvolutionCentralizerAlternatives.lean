module

public import CFSG.CharacterTheory.Semidihedral.Local.DerivedInvolutionsConjugate
public import CFSG.CharacterTheory.Semidihedral.Local.FourSubgroupCentralizerSplit
public import CFSG.CharacterTheory.Semidihedral.CentralQuotients

public section

namespace CFSG.Semidihedral.Local

open CFSG.Open
open scoped Pointwise

variable {G : Type*} [Group G]


theorem self_mem_center_centralizer (t : G) :
    (⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ : Subgroup.centralizer {t}) ∈
      Subgroup.center (Subgroup.centralizer {t}) :=
  Subgroup.mem_center_iff.mpr fun x =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2)


end CFSG.Semidihedral.Local
