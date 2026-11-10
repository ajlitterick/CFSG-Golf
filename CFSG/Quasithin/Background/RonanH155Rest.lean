module

public import CFSG.Quasithin.Background.RonanH163Vocab

public section

namespace CFSG.Quasithin.RonanH155

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.RonanH163 CFSG.Quasithin.RonanH143

@[expose] def restrictAutHom {G : Type*} [Group G] {V : Type*} [CommGroup V] (ρ : G →* MulAut V)
    (W : Subgroup V) (hW : ∀ g : G, ∀ w ∈ W, ρ g w ∈ W) : G →* MulAut ↥W where
  toFun g :=
    { toFun := fun w => ⟨ρ g (w : V), hW g w w.2⟩
      invFun := fun w => ⟨ρ g⁻¹ (w : V), hW g⁻¹ w w.2⟩
      left_inv := fun w => by
        apply Subtype.ext
        show ρ g⁻¹ (ρ g (w : V)) = w
        rw [map_inv, MulAut.inv_apply_self]
      right_inv := fun w => by
        apply Subtype.ext
        show ρ g (ρ g⁻¹ (w : V)) = w
        rw [map_inv, MulAut.apply_inv_self]
      map_mul' := fun a b => Subtype.ext (map_mul (ρ g) (a : V) (b : V)) }
  map_one' := by
    ext w
    show ρ 1 (w : V) = w
    rw [map_one, MulAut.one_apply]
  map_mul' := fun g g' => by
    ext w
    show ρ (g * g') (w : V) = ρ g (ρ g' (w : V))
    rw [map_mul, MulAut.mul_apply]


end CFSG.Quasithin.RonanH155
