module

public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

universe u v

variable {k : Type u} [Semiring k] {G : Type v} [Group G]

namespace CFSG.ClassFun

open Classical in
/-- The explicit linear equivalence between ClassFun and functions on ConjClasses. -/
@[expose] noncomputable def linearEquivConjClasses :
    ClassFun k G ≃ₗ[k] (ConjClasses G → k) where
  toFun f := Quotient.lift f.toFun f.map_conj
  invFun F :=
    { toFun := fun g => F (Quotient.mk _ g)
      map_conj := fun x y h => by
        -- `Quotient.sound` turns `IsConj x y` into `Quotient.mk _ x = Quotient.mk _ y`
        rw [Quotient.sound h] }
  left_inv f := by ext x; rfl
  right_inv F := by ext q; revert q; exact Quotient.ind (fun x => rfl)
  map_add' f g := by ext q; revert q; exact Quotient.ind (fun x => rfl)
  map_smul' m f := by ext q; revert q; exact Quotient.ind (fun x => rfl)

open Classical in
noncomputable instance instFintypeConjClasses
    {G : Type v} [Group G] [Fintype G] :
    Fintype (ConjClasses G) :=
  Quotient.fintype (IsConj.setoid G)


end CFSG.ClassFun
