module

public import CFSG.Foundations.MaxCardThompson
public import CFSG.Foundations.MaxOrderThompsonDefs
import CFSG.Foundations.MaxOrderThompson
public import CFSG.Open.LocalVocabulary

public section

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {ImageType : Type imageUniverse} [Group ImageType] [Finite ImageType]

@[expose, reducible] def maximumOrderAbelianFamily (GroupType : Type groupUniverse) [Group GroupType] :
    Set (Subgroup GroupType) :=
  {target | CFSG.IsMaxCardAbelian target}


@[expose, reducible] def orderThompsonSubgroup (GroupType : Type groupUniverse) [Group GroupType] :
    Subgroup GroupType :=
  CFSG.maxCardThompson GroupType

@[expose, reducible] def orderThompsonCenter (GroupType : Type groupUniverse) [Group GroupType] :
    Subgroup GroupType :=
  CFSG.maxCardZJ GroupType

omit [Finite GroupType] in
private theorem orderThompsonSubgroup_eq_canonical (GroupType : Type groupUniverse) [Group GroupType] :
    orderThompsonSubgroup GroupType = CFSG.maxCardThompson GroupType :=
  rfl

omit [Finite GroupType] in
private theorem orderThompsonCenter_eq_canonical (GroupType : Type groupUniverse) [Group GroupType] :
    orderThompsonCenter GroupType = CFSG.maxCardZJ GroupType :=
  rfl


omit [Finite GroupType] [Finite ImageType] in
theorem maximum_order_abelian_family_map (equivalence : GroupType ≃* ImageType)
    (target : Subgroup GroupType) (member : target ∈ maximumOrderAbelianFamily GroupType) :
    target.map equivalence.toMonoidHom ∈ maximumOrderAbelianFamily ImageType :=
  CFSG.IsMaxCardAbelian.map_mulEquiv equivalence member


omit [Finite GroupType] [Finite ImageType] in
theorem order_thompson_subgroup_map (equivalence : GroupType ≃* ImageType) :
    (orderThompsonSubgroup GroupType).map equivalence.toMonoidHom = orderThompsonSubgroup ImageType := by
  rw [orderThompsonSubgroup_eq_canonical, orderThompsonSubgroup_eq_canonical]
  exact CFSG.maxCardThompson_map_mulEquiv equivalence


omit [Finite GroupType] [Finite ImageType] in
theorem order_thompson_center_map (equivalence : GroupType ≃* ImageType) :
    (orderThompsonCenter GroupType).map equivalence.toMonoidHom = orderThompsonCenter ImageType := by
  rw [orderThompsonCenter_eq_canonical, orderThompsonCenter_eq_canonical]
  exact CFSG.maxCardZJ_map_mulEquiv equivalence


end CFSG.SignalizerFunctor.Helpers
