module

public import CFSG.LocalAnalysis.ComponentInitial.FactorwiseFixedLayer

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

section Transport

variable {G G' : Type*} [Group G] [Group G']

theorem isComponentOf_map_iff {f : G →* G'} (hf : Function.Injective f) {Q K : Subgroup G} :
    CFSG.Assembly.IsComponentOf (Q.map f) (K.map f) ↔ CFSG.Assembly.IsComponentOf Q K := by
  have hq : CFSG.Assembly.IsQuasisimple (Q.map f) ↔ CFSG.Assembly.IsQuasisimple Q := by
    rw [AssemblyBPredicates.isQuasisimple_iff_native, AssemblyBPredicates.isQuasisimple_iff_native]
    exact (isQuasisimple_congr (Q.equivMapOfInjective f hf)).symm
  refine ⟨fun h => ⟨(map_le_map_iff_of_injective hf).1 h.1, ?_, hq.1 h.2.2⟩,
    fun h => ⟨map_mono h.1, assembly_isSubnormal_map f h.2.1, hq.2 h.2.2⟩⟩
  have := assembly_isSubnormal_comap f h.2.1
  rwa [Subgroup.comap_map_eq_self_of_injective hf,
    Subgroup.comap_map_eq_self_of_injective hf] at this

end Transport

variable {T : Type*} [Group T]


section Solvable

variable {G G' : Type*} [Group G] [Group G']


theorem isSolvable_congr (e : G ≃* G') : Group.IsSolvable G ↔ Group.IsSolvable G' :=
  ⟨fun _ => Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective,
    fun _ => Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

end Solvable


end CFSG.LocalAnalysis.ComponentInitial
