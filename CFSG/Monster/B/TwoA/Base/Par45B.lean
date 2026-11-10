
module

public import CFSG.Monster.B.TwoA.Base.Par45BBase

public import CFSG.Monster.B.TwoA.Base.Par45A
public import CFSG.Monster.B.TwoA.Base.RankThree

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.Lifts CFSG.Monster.VisCert


theorem chain_flags :
    ∀ j i : ℕ, 1 ≤ j → j < i → i ≤ 5 →
    (∀ g : Kchain i, (g : Dfull) ∈ Kchain j ↔
      ∀ e : Echain i, (e : Dfull) ∈ Echain j →
        ((conjE (Echain i) g e : Echain i) : Dfull) ∈ Echain j) ∧
    ((Kchain j ⊓ Kchain i).subgroupOf (Kchain i)).index =
      Nat.card (SubspaceDim (ZMod 2) (Fin i → ZMod 2) j) := by
  intro j i hj hji hi
  have hi2 : 2 ≤ i := by omega
  interval_cases i <;> interval_cases j
  · exact flag_pair (E := Vhat) (F := Subgroup.zpowers xhat) natCard_Vhat_pow
      natCard_zpowers_xhat (Subgroup.zpowers_le.2 xhat_mem_Vhat) conjE_Vhat_surjective
  · exact flag_pair (E := E3) (F := Subgroup.zpowers xhat) natCard_E3_pow
      natCard_zpowers_xhat (Subgroup.zpowers_le.2 xhat_mem_E3) conjE_E3_surjective
  · exact flag_pair (E := E3) (F := Vhat) natCard_E3_pow natCard_Vhat_pow Vhat_le_E3
      conjE_E3_surjective
  · exact flag_pair (E := E4) (F := Subgroup.zpowers xhat) natCard_E4
      natCard_zpowers_xhat (Subgroup.zpowers_le.2 xhat_mem_E4) conjE_E4_surjective
  · exact flag_pair (E := E4) (F := Vhat) natCard_E4 natCard_Vhat_pow
      (Vhat_le_E3.trans E3_le_E4) conjE_E4_surjective
  · exact flag_pair (E := E4) (F := E3) natCard_E4 natCard_E3_pow E3_le_E4
      conjE_E4_surjective
  · exact flag_pair (E := E5) (F := Subgroup.zpowers xhat) natCard_E5
      natCard_zpowers_xhat (Subgroup.zpowers_le.2 xhat_mem_E5) conjE_E5_surjective
  · exact flag_pair (E := E5) (F := Vhat) natCard_E5 natCard_Vhat_pow
      ((Vhat_le_E3.trans E3_le_E4).trans E4_le_E5) conjE_E5_surjective
  · exact flag_pair (E := E5) (F := E3) natCard_E5 natCard_E3_pow (E3_le_E4.trans E4_le_E5)
      conjE_E5_surjective
  · exact flag_pair (E := E5) (F := E4) natCard_E5 natCard_E4 E4_le_E5 conjE_E5_surjective


end CFSG.Monster.B.TwoA
