module

public import CFSG.Quasithin.Vol2.Ch11SecBNPE114
public import CFSG.Quasithin.Background.E2Two
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open

theorem TypeOne.isSimpleGroup {Y : Type} [Group Y] (h : TypeOne Y) : IsSimpleGroup Y := by
  rcases h with h | h | ⟨p, f, -, -, -, h⟩ | ⟨s, p, -, -, h⟩
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 3 2 1 h).2
  · obtain ⟨e⟩ : Nonempty (Y ≃* alternatingGroup (Fin 6)) := h
    have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 2 p f h).2
  · cases s with
    | true => exact (CFSG.LieType.Simplicity.fam_PSL_simplicity Y 3 p 1 h).2
    | false => exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity Y 3 p 1 h).2


end CFSG.Quasithin.Vol2.Ch11.SecB
