module

public import CFSG.Quasithin.SteinbergCBSevenPoints
public import CFSG.Quasithin.SteinbergCBAlternatingFive

public section

namespace CFSG.Quasithin.SteinbergCB

open Equiv Equiv.Perm Subgroup
open scoped Pointwise


theorem nat_card_sevenP : Nat.card sevenP = 16 := by
  rw [← sevenA_inf_sevenB, ← card_filter_sevenCond, ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun g => ?_)
  rw [Subgroup.mem_inf, mem_sevenA, mem_sevenB, sevenCond]


end CFSG.Quasithin.SteinbergCB
