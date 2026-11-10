module

public import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonMaxOrder
public import CFSG.Foundations.MaxOrderThompson

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable (GroupType : Type groupUniverse) [Group GroupType]


theorem order_thompson_center_eq_maxCardZJ :
    orderThompsonCenter GroupType = CFSG.maxCardZJ GroupType :=
  rfl

variable [Finite GroupType]

theorem maximum_order_abelian_family_eq_maxOrderAbelianFamily :
    maximumOrderAbelianFamily GroupType = CFSG.maxOrderAbelianFamily GroupType :=
  CFSG.setOf_isMaxCardAbelian_eq


theorem order_thompson_center_eq_orderZJ :
    orderThompsonCenter GroupType = CFSG.orderZJ GroupType :=
  (order_thompson_center_eq_maxCardZJ GroupType).trans CFSG.maxCardZJ_eq_orderZJ

end CFSG.SignalizerFunctor.Helpers
