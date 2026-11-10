module

public import CFSG.Monster.B.GSide.TwoDNative
public import CFSG.Monster.B.GSide.TwoDNativeOrder

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.GSide

open CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8

theorem P4pS_le_centralizer_t2DS :
    P4pS ≤ Subgroup.centralizer {t2DS} := fun _ hx =>
  Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext
    (Subgroup.mem_centralizer_singleton_iff.1 (mem_P4pS.1 hx).2))

theorem P4p_le_Shat :
    P4p ≤ Shat := P4p_le_Xgrp.trans Xgrp_le_Shat

theorem natCard_P4pS :
    Nat.card P4pS = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := by
  rw [P4pS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe P4p_le_Shat).toEquiv, natCard_P4p]
  norm_num

theorem P4pS_le_normalizer_T9S :
    P4pS ≤ Subgroup.normalizer (T9S : Set Shat) := by
  intro x hx
  have hX : (x : Dfull) ∈ Subgroup.normalizer (T9 : Set Dfull) :=
    Xgrp_le_normalizer_T9 (P4p_le_Xgrp (mem_P4pS.1 hx))
  rw [Subgroup.mem_normalizer_iff] at hX ⊢
  intro y
  rw [mem_T9S, mem_T9S]
  exact hX y

theorem centralizer_t2DS_eq :
    Subgroup.centralizer {t2DS} = P4pS :=
  centralizer_eq_of_le_of_natCard orderOf_t2DS rankS_t2DS P4pS_le_centralizer_t2DS natCard_P4pS

theorem centralizer_t2DS_le_normalizer :
    Subgroup.centralizer {t2DS} ≤ Subgroup.normalizer (T9S : Set Shat) :=
  centralizer_le_normalizer_of_le_of_natCard orderOf_t2DS rankS_t2DS P4pS_le_centralizer_t2DS
    natCard_P4pS P4pS_le_normalizer_T9S

theorem natCard_centralizer_t2DS :
    Nat.card (Subgroup.centralizer {t2DS}) = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := by
  rw [centralizer_t2DS_eq, natCard_P4pS]

end CFSG.Monster.B.GSide
