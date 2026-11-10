module

public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Algebra.Field.ZMod


public section

namespace CFSG.Quasithin.RuType.GL25

abbrev W42 : Type := Multiplicative (ZMod 4) ≀ᵣ Multiplicative (ZMod 2)

instance : DecidableEq W42 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right)
    (by
      constructor
      · rintro ⟨h1, h2⟩; exact RegularWreathProduct.ext h1 h2
      · rintro rfl; exact ⟨rfl, rfl⟩)

instance : Fintype W42 := Fintype.ofEquiv _ (RegularWreathProduct.equivProd _ _).symm

@[expose] def u4 (k : Multiplicative (ZMod 4)) : ZMod 5 := 2 ^ (Multiplicative.toAdd k).val

@[expose] def z2 (q : Multiplicative (ZMod 2)) : Fin 2 := Multiplicative.toAdd q

@[expose] def ofz2 (x : Fin 2) : Multiplicative (ZMod 2) := Multiplicative.ofAdd x

@[expose] def Ψ0 (a : W42) : Matrix (Fin 2) (Fin 2) (ZMod 5) :=
  Matrix.of fun x y => if x = z2 a.right + y then u4 (a.left (ofz2 x)) else 0

theorem Ψ0_mul : ∀ a b : W42, Ψ0 (a * b) = Ψ0 a * Ψ0 b := by decide +kernel

theorem Ψ0_one : Ψ0 1 = 1 := by decide +kernel


@[expose] def Ψm : W42 →* Matrix (Fin 2) (Fin 2) (ZMod 5) where
  toFun := Ψ0
  map_one' := Ψ0_one
  map_mul' := Ψ0_mul

@[expose] def Ψ : W42 →* GL (Fin 2) (ZMod 5) := Ψm.toHomUnits


section Faithful


end Faithful

end CFSG.Quasithin.RuType.GL25
