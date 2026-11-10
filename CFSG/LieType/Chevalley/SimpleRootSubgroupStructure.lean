module

public import CFSG.LieType.Chevalley.SimpleRootSubgroups

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley

variable (τ : Tag) (K : Type*) [Field K]

@[expose] def simplePosHom
    (i : Fin τ.rank) : Multiplicative K →* simplePosSubgroup τ K i where
  toFun c := ⟨⟨xUnit τ K i c.toAdd, xUnit_mem_adjointGroup i _⟩, c.toAdd, rfl⟩
  map_one' := Subtype.ext (Subtype.ext (xUnit_zero i))
  map_mul' a b := Subtype.ext (Subtype.ext (xUnit_add i a.toAdd b.toAdd))

@[expose] def simpleNegHom
    (i : Fin τ.rank) : Multiplicative K →* simpleNegSubgroup τ K i where
  toFun c := ⟨⟨yUnit τ K i c.toAdd, yUnit_mem_adjointGroup i _⟩, c.toAdd, rfl⟩
  map_one' := Subtype.ext (Subtype.ext (yUnit_zero i))
  map_mul' a b := Subtype.ext (Subtype.ext (yUnit_add i a.toAdd b.toAdd))

variable {τ K}


theorem iSup_simplePosSubgroup_sup_simpleNegSubgroup :
    ⨆ i, (simplePosSubgroup τ K i ⊔ simpleNegSubgroup τ K i) = ⊤ := by
  refine (Subgroup.map_injective (adjointGroup τ K).subtype_injective) (le_antisymm
    (Subgroup.map_mono le_top) ?_)
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨i, c, hg | hg⟩
  · have hx : g = xUnit τ K i c := Units.ext hg
    subst hx
    exact ⟨⟨_, xUnit_mem_adjointGroup i c⟩, Subgroup.mem_iSup_of_mem i
      (Subgroup.mem_sup_left ⟨c, rfl⟩), rfl⟩
  · have hy : g = yUnit τ K i c := Units.ext hg
    subst hy
    exact ⟨⟨_, yUnit_mem_adjointGroup i c⟩, Subgroup.mem_iSup_of_mem i
      (Subgroup.mem_sup_right ⟨c, rfl⟩), rfl⟩


end CFSG.LieType.Chevalley
