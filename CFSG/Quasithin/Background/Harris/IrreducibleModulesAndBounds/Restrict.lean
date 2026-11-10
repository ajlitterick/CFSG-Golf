module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

private theorem map_eq_of_invariant {K : Subgroup (GLV V)} {W : Submodule (ZMod 2) V}
    (hW : Invariant K W) (k : K) :
    W.map ((k : GLV V) : V →ₛₗ[RingHom.id (ZMod 2)] V) = W := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    exact hW k k.2 w hw
  · intro w hw
    refine ⟨(k : GLV V).symm w, hW (k : GLV V)⁻¹ (inv_mem k.2) w hw, ?_⟩
    simp

noncomputable def restrictHom (K : Subgroup (GLV V)) (W : Submodule (ZMod 2) V)
    (hW : Invariant K W) : ↥K →* GLV ↥W where
  toFun k := (k : GLV V).ofSubmodules W W (map_eq_of_invariant hW k)
  map_one' := by ext x; simp
  map_mul' a b := by ext x; simp

theorem restrictHom_apply (K : Subgroup (GLV V)) (W : Submodule (ZMod 2) V)
    (hW : Invariant K W) (k : K) (w : W) :
    ((restrictHom K W hW k w : W) : V) = (k : GLV V) (w : V) := by
  simp [restrictHom]

noncomputable def quotientHom (K : Subgroup (GLV V)) (W : Submodule (ZMod 2) V)
    (hW : Invariant K W) : ↥K →* GLV (V ⧸ W) where
  toFun k := Submodule.Quotient.equiv W W (k : GLV V) (map_eq_of_invariant hW k)
  map_one' := by
    ext x
    induction x using Submodule.Quotient.induction_on
    simp [Submodule.Quotient.equiv_apply]
  map_mul' a b := by
    ext x
    induction x using Submodule.Quotient.induction_on
    simp [Submodule.Quotient.equiv_apply]

theorem quotientHom_apply (K : Subgroup (GLV V)) (W : Submodule (ZMod 2) V)
    (hW : Invariant K W) (k : K) (v : V) :
    quotientHom K W hW k (Submodule.Quotient.mk v) = Submodule.Quotient.mk ((k : GLV V) v) := by
  simp [quotientHom, Submodule.Quotient.equiv_apply]


end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
