module

public import CFSG.Monster.B.Rep4371.TauRow

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess

theorem mem_oddCodes_iff (a : ℕ) :
    a ∈ Model.oddCodes.toList ↔
      a < 4096 ∧ a % 2 = 0 ∧ (Model.wordN a).testBit 0 = (Model.wordN a).testBit 1 := by
  simp only [Model.oddCodes, Model.oddCodesOf, List.toList_toArray, List.mem_filter, List.mem_map,
    List.mem_range, beq_iff_eq]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, h⟩
    exact ⟨by omega, by omega, h⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨a / 2, by omega, by omega⟩, h3⟩

theorem oddCodes_sorted : Model.oddCodes.toList.Pairwise (· < ·) := by
  rw [Model.oddCodes, Model.oddCodesOf, List.toList_toArray]
  refine List.Pairwise.filter _ ?_
  rw [List.pairwise_map]
  exact List.pairwise_lt_range.imp fun h => by omega

theorem oddCodes_size : Model.oddCodes.size = 1024 := by decide +kernel

theorem mem_octCoeffs_iff (a : ℕ) :
    a ∈ Model.octCoeffs.toList ↔
      a < 4096 ∧ Model.popcN 24 (Model.wordN a) = 8 ∧ Model.wordN a % 4 = 3 := by
  simp only [Model.octCoeffs, Model.octCoeffsOf, List.toList_toArray, List.mem_mergeSort,
    List.mem_filter, List.mem_range, Bool.and_eq_true, beq_iff_eq]


end CFSG.Monster.B.Rep4371
