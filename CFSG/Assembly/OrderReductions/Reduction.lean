module

public import CFSG.Assembly.OrderReductions.StrongEmbedding

public section

open CFSG.Open

namespace CFSG.OrderReductions.Reduction


theorem proper_subgroup_card_lt (group : Type*) [Group group] [Finite group]
    (subgroup : Subgroup group) (proper : subgroup ≠ ⊤) :
    Nat.card subgroup < Nat.card group := by
  apply Nat.lt_of_le_of_ne (subgroup.card_le_card_group)
  intro equal_card
  exact proper (subgroup.eq_top_of_card_eq equal_card)


end CFSG.OrderReductions.Reduction
