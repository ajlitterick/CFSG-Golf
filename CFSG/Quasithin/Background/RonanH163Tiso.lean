module

public import CFSG.Quasithin.Background.RonanH163Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143

variable {V V' : Type*} [CommGroup V] [CommGroup V']


theorem e_toMonoidHom_injective (e : V ≃* V') : Function.Injective (e.toMonoidHom : V →* V') :=
  e.injective


theorem rk_map (e : V ≃* V') (U : Subgroup V) : rk ↥(U.map e.toMonoidHom) = rk ↥U := by
  have h : Nat.card ↥(U.map e.toMonoidHom) = Nat.card ↥U :=
    (Nat.card_congr (U.equivMapOfInjective e.toMonoidHom (e_toMonoidHom_injective e)).toEquiv).symm
  unfold CFSG.Quasithin.rk
  rw [h]


section Rep


end Rep


end CFSG.Quasithin.RonanH163
