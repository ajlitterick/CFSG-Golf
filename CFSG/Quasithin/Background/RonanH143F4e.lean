module

public import CFSG.Quasithin.Background.RonanH143F4c
public import CFSG.Quasithin.Background.RonanH143F4d
public import CFSG.Quasithin.Background.RonanH143F4a

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf

@[expose] def conjAut {X : Type*} [Group X] (G K : Subgroup X) (h : ∀ g ∈ G, ∀ k ∈ K, g * k * g⁻¹ ∈ K) :
    ↥G →* MulAut ↥K where
  toFun g :=
    { toFun := fun k => ⟨(g : X) * k * (g : X)⁻¹, h g g.2 k k.2⟩
      invFun := fun k => ⟨(g : X)⁻¹ * k * (g : X), by
        simpa using h (g : X)⁻¹ (G.inv_mem g.2) k k.2⟩
      left_inv := fun k => by
        apply Subtype.ext
        simp [mul_assoc]
      right_inv := fun k => by
        apply Subtype.ext
        simp [mul_assoc]
      map_mul' := fun k l => by
        apply Subtype.ext
        simp [mul_assoc] }
  map_one' := by
    ext k
    simp
  map_mul' g g' := by
    ext k
    simp [mul_assoc]


end CFSG.Quasithin.RonanH143
