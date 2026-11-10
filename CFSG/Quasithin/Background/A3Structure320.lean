
module

public import CFSG.Quasithin.Background.A3Structure320Core
public import CFSG.Quasithin.Background.A3StructureBasic

public section

namespace CFSG.Quasithin

namespace A320

open CFSG.Open CFSG.SectionRank
open scoped commutatorElement


theorem isSolvable_pCore_two (H : Type*) [Group H] [Finite H] :
    Group.IsSolvable ↥(CFSG.pCore 2 H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥(CFSG.pCore 2 H) := IsPGroup.isNilpotent CFSG.pCore_isPGroup
  infer_instance

theorem map_solvRad_le {H Q : Type*} [Group H] [Finite H] [Group Q] (π : H →* Q)
    (L : Subgroup H) : (solvRad L).map π ≤ solvRad (L.map π) := by
  refine le_solvRad (Subgroup.map_mono (solvRad_le L)) ?_ ?_
  · rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono (solvRad_le L))]
    rintro _ _ ⟨r, hr, rfl⟩ ⟨l, hl, rfl⟩
    refine ⟨l * r * l⁻¹, conj_mem_solvRad (Subgroup.le_normalizer hl) hr, ?_⟩
    simp
  · have : Group.IsSolvable ↥(solvRad L) := solvRad_isSolvable L
    exact Group.isSolvable_of_surjective (π.subgroupMap_surjective (solvRad L))


end A320


namespace A320


end A320


end CFSG.Quasithin
