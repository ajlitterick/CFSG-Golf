module

public import CFSG.RankThree.PartTwo.Sec21.Item22Tools
public import CFSG.RankThree.PartTwo.Sec21.Item22Equivariance
public import CFSG.RankThree.PartTwo.KFacts.KP14MonomialStructure
public import CFSG.RankThree.PartTwo.Sec21.Item22Statements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts.KP14
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly (IsElemAbelian)
open CFSG.LocalAnalysis.GorensteinLyons (IsThreeTranspositions IsThreeFourPlusTranspositions)

variable {G : Type} [Group G]

theorem dStar_subset_wStar (A : Subgroup G) : dStar A ⊆ wStar A := fun _ hφ => by
  obtain ⟨-, X, -, hφX⟩ := hφ
  exact starOf_le_wStar A X hφX

theorem closure_dStar_le_wStar (A : Subgroup G) : Subgroup.closure (dStar A) ≤ wStar A :=
  (Subgroup.closure_le _).mpr (dStar_subset_wStar A)

theorem conj_mem_dStar_of_mem_wStar [Finite G] {A : Subgroup G} {g : MulAut A}
    (hg : g ∈ wStar A) {φ : MulAut A} (hφ : φ ∈ dStar A) : g * φ * g⁻¹ ∈ dStar A := by
  obtain ⟨w, rfl⟩ := hg
  exact conj_mem_dStar w hφ

theorem not_isMulCommutative_perm_three : ¬ IsMulCommutative (Equiv.Perm (Fin 3)) := by
  intro h
  have := h.is_comm.comm (Equiv.swap 0 1) (Equiv.swap 1 2)
  revert this
  decide

theorem not_isMulCommutative_dihedral_four : ¬ IsMulCommutative (DihedralGroup 4) := by
  intro h
  have := h.is_comm.comm (DihedralGroup.r 1) (DihedralGroup.sr 0)
  revert this
  decide

theorem isMulCommutative_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : IsMulCommutative X) : IsMulCommutative Y :=
  ⟨⟨fun a b => by
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact h.is_comm.comm _ _⟩⟩


end CFSG.RankThree.PartTwo.Sec21
