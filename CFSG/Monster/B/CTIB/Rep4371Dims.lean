module

public import CFSG.Monster.B.CTIB.Rep4371Rho
public import CFSG.Monster.B.Rep4371.Glue
public import CFSG.Monster.B.Rep4371.RBasis

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.SpinLattice
  CFSG.Monster.Spin CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.B.Rep4371


theorem Across_eq_span :
    Across isShortCoord_rStar = Submodule.span ℚ (Set.range fun k : Fin 23 => Rraw k) :=
  le_antisymm Across_le_span (Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact Rraw_mem_Across (by omega)))

theorem Tplus_eq_span :
    Tplus isShortCoord_rStar = Submodule.span ℚ (Set.range fun t : Fin 2048 => Rraw (2323 + t)) :=
  le_antisymm Tplus_le_span (Submodule.span_le.2 (by
    rintro _ ⟨t, rfl⟩
    exact Rraw_mem_Tplus (by omega)))


theorem iSupIndep_comap_subtype {M : Type*} [AddCommGroup M] [Module ℚ M] (N : Submodule ℚ M)
    {ι : Type*} {p : ι → Submodule ℚ M} (h : iSupIndep p) :
    iSupIndep fun i => (p i).comap N.subtype := by
  intro i
  rw [Submodule.disjoint_def]
  intro v hv hv'
  have hle : (⨆ j, ⨆ (_ : j ≠ i), (p j).comap N.subtype) ≤
      (⨆ j, ⨆ (_ : j ≠ i), p j).comap N.subtype :=
    iSup₂_le fun j hj => Submodule.comap_mono (le_iSup₂ (f := fun j (_ : j ≠ i) => p j) j hj)
  exact Subtype.ext (Submodule.disjoint_def.1 (h i) _ hv (hle hv'))


end CFSG.Monster.B.CTIB
