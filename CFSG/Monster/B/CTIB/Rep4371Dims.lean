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

theorem linearIndependent_RrawA :
    LinearIndependent ℚ (fun k : Fin 23 => Rraw k) := by
  have h := (linearIndependent_Rraw octDataOK_true).comp (fun k : Fin 23 => (⟨k, by omega⟩ :
    Fin 4371)) (fun k k' h => Fin.ext (by simpa using congrArg Fin.val h))
  exact h

theorem linearIndependent_RrawT :
    LinearIndependent ℚ (fun t : Fin 2048 => Rraw (2323 + t)) := by
  have h := (linearIndependent_Rraw octDataOK_true).comp
    (fun t : Fin 2048 => (⟨2323 + t, by omega⟩ :
    Fin 4371)) (fun t t' h => Fin.ext (by have := congrArg Fin.val h; simp only at this; omega))
  exact h

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

theorem finrank_Across :
    Module.finrank ℚ (Across isShortCoord_rStar) = 23 := by
  rw [Across_eq_span, finrank_span_eq_card linearIndependent_RrawA, Fintype.card_fin]

theorem finrank_Xdiff :
    Module.finrank ℚ (Xdiff isShortCoord_rStar) = 2300 := by
  rw [← (xdiff_Rraw octDataOK_true).2.1,
    finrank_span_eq_card (xdiff_Rraw octDataOK_true).1, Fintype.card_fin]

theorem finrank_Tplus :
    Module.finrank ℚ (Tplus isShortCoord_rStar) = 2048 := by
  rw [Tplus_eq_span, finrank_span_eq_card linearIndependent_RrawT, Fintype.card_fin]


theorem Vst_eq_sup :
    Vst = Across isShortCoord_rStar ⊔ Xdiff isShortCoord_rStar ⊔ Tplus isShortCoord_rStar :=
  V4_eq_sup isShortCoord_rStar

theorem Across_le_Vst : Across isShortCoord_rStar ≤ Vst := by
  rw [Vst_eq_sup]
  exact le_sup_left.trans le_sup_left

theorem Xdiff_le_Vst : Xdiff isShortCoord_rStar ≤ Vst := by
  rw [Vst_eq_sup]
  exact le_sup_right.trans le_sup_left

theorem Tplus_le_Vst : Tplus isShortCoord_rStar ≤ Vst := by
  rw [Vst_eq_sup]
  exact le_sup_right

theorem finrank_V23 : Module.finrank ℚ V23 = 23 :=
  (Submodule.comapSubtypeEquivOfLe Across_le_Vst).finrank_eq.trans finrank_Across

theorem finrank_V2300 : Module.finrank ℚ V2300 = 2300 :=
  (Submodule.comapSubtypeEquivOfLe Xdiff_le_Vst).finrank_eq.trans finrank_Xdiff

theorem finrank_V2048 : Module.finrank ℚ V2048 = 2048 :=
  (Submodule.comapSubtypeEquivOfLe Tplus_le_Vst).finrank_eq.trans finrank_Tplus

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
