module

public import CFSG.LieType.Chevalley.C2E6UnitaryFourFrobenius
public import CFSG.LieType.Chevalley.C2E6MinusSixForm
public import CFSG.LieType.Chevalley.C2E6MinusSixBase
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Overlap

open Module Matrix CFSG.Fischer

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


theorem bijOn_pointMap :
    Set.BijOn pointMap {P : Submodule K V | IsTotallyIsotropic P ∧ finrank K P = 2}
      {U : Submodule (ZMod 2) X | IsTotallySingular U ∧ finrank (ZMod 2) U = 1} := by
  refine ⟨fun P ⟨hP, h2⟩ => ?_, fun P ⟨hP, h2⟩ P' ⟨hP', h2'⟩ h => ?_, fun U ⟨hU, h1⟩ => ?_⟩
  · obtain ⟨j, rfl⟩ := exists_uPlane_eq hP h2
    rw [Set.mem_ofPred_eq, pointMap_uPlane]
    exact ⟨isTotallySingular_ptSub _, finrank_ptSub _⟩
  · obtain ⟨j, rfl⟩ := exists_uPlane_eq hP h2
    obtain ⟨j', rfl⟩ := exists_uPlane_eq hP' h2'
    rw [pointMap_uPlane, pointMap_uPlane] at h
    rw [sigma_injective (ptSub_injective h)]
  · obtain ⟨i, rfl⟩ := exists_ptSub_eq hU h1
    obtain ⟨j, rfl⟩ := sigma_surjective i
    exact ⟨uPlane j, ⟨isTotallyIsotropic_uPlane j, finrank_uPlane j⟩, pointMap_uPlane j⟩

theorem bijOn_lineMap :
    Set.BijOn lineMap {ℓ : Submodule K V | IsTotallyIsotropic ℓ ∧ finrank K ℓ = 1}
      {U : Submodule (ZMod 2) X | IsTotallySingular U ∧ finrank (ZMod 2) U = 2} := by
  refine ⟨fun ℓ ⟨hℓ, h1⟩ => ?_, fun ℓ ⟨hℓ, h1⟩ ℓ' ⟨hℓ', h1'⟩ h => ?_, fun U ⟨hU, h2⟩ => ?_⟩
  · obtain ⟨k, rfl⟩ := exists_uLine_eq hℓ h1
    rw [Set.mem_ofPred_eq, lineMap_uLine]
    exact ⟨isTotallySingular_lnSub _, finrank_lnSub _⟩
  · obtain ⟨k, rfl⟩ := exists_uLine_eq hℓ h1
    obtain ⟨k', rfl⟩ := exists_uLine_eq hℓ' h1'
    rw [lineMap_uLine, lineMap_uLine] at h
    rw [tau_injective (lnSub_injective h)]
  · obtain ⟨j, rfl⟩ := exists_lnSub_eq hU h2
    obtain ⟨k, rfl⟩ := tau_surjective j
    exact ⟨uLine k, ⟨isTotallyIsotropic_uLine k, finrank_uLine k⟩, lineMap_uLine k⟩

theorem le_iff_pointMap_le_lineMap {ℓ P : Submodule K V} (hℓ : IsTotallyIsotropic ℓ)
    (h1 : finrank K ℓ = 1) (hP : IsTotallyIsotropic P) (h2 : finrank K P = 2) :
    ℓ ≤ P ↔ pointMap P ≤ lineMap ℓ := by
  obtain ⟨k, rfl⟩ := exists_uLine_eq hℓ h1
  obtain ⟨j, rfl⟩ := exists_uPlane_eq hP h2
  rw [uLine_le_uPlane_iff, pointMap_uPlane, lineMap_uLine, ptSub_le_lnSub_iff, uOn_iff_ptOn]


theorem uVec_zero : uVec 0 = u 0 := by decide


theorem finrank_two_of_ne_one {x : UVertex} (h : finrank K x.1 ≠ 1) : finrank K x.1 = 2 :=
  x.2.2.resolve_left h

@[expose] def dualMap (x : UVertex) : QVertex :=
  if h : finrank K x.1 = 1 then
    ⟨lineMap x.1, (bijOn_lineMap.mapsTo ⟨x.2.1, h⟩).1,
      Or.inr (bijOn_lineMap.mapsTo ⟨x.2.1, h⟩).2⟩
  else
    ⟨pointMap x.1, (bijOn_pointMap.mapsTo ⟨x.2.1, finrank_two_of_ne_one h⟩).1,
      Or.inl (bijOn_pointMap.mapsTo ⟨x.2.1, finrank_two_of_ne_one h⟩).2⟩


end CFSG.LieType.Chevalley.C2E6Overlap
