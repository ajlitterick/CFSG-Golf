module

public import CFSG.Quasithin.EmptyFaithful.S153ZE

public section

namespace CFSG.Quasithin.RonanD39

open scoped Pointwise
open CFSG.Quasithin.Z391

section Count

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]


end Count

section Chain

variable {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q] [MulDistribMulAction Γ Q]

inductive LChain (Λ : Subgroup Γ) (d : ℕ) : Subgroup Q → Subgroup Q → ℕ → Prop
  | refl (X : Subgroup Q) : LChain Λ d X X 0
  | snoc {X Y Z : Subgroup Q} {k : ℕ} : LChain Λ d X Y k → XMod.IsInv ↥Λ Y → XMod.IsInv ↥Λ Z →
      XMod.IsIrrSec ↥Λ Y Z → rk ↥Z = rk ↥Y + d → LChain Λ d X Z (k + 1)

variable {Λ : Subgroup Γ} {d : ℕ}

theorem LChain.trans {X Y Z : Subgroup Q} {k l : ℕ} (h₁ : LChain Λ d X Y k)
    (h₂ : LChain Λ d Y Z l) : LChain Λ d X Z (k + l) := by
  induction h₂ with
  | refl => simpa using h₁
  | snoc _ hY hZ hYZ hrk ih => exact LChain.snoc ih hY hZ hYZ hrk


theorem LChain.le {X Y : Subgroup Q} {k : ℕ} (h : LChain Λ d X Y k) : X ≤ Y := by
  induction h with
  | refl => exact le_rfl
  | snoc _ _ _ hYZ _ ih => exact ih.trans hYZ.1.le


end Chain

section Hom


end Hom

section SubgroupOf


end SubgroupOf

end CFSG.Quasithin.RonanD39
