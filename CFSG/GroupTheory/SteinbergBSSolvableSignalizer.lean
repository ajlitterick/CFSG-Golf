module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.GroupTheory.Solvable

public section

namespace CFSG.GroupTheory.SteinbergBS

structure IsSolvableSignalizerDatum (p : ℕ) (A : Type*) [Group A] (G : Type*) [Group G]
    (α : A →* MulAut G) (θ : A → Subgroup G) : Prop where
  prime : p.Prime
  finite_actor : Finite A
  elementary : IsElementaryAbelian p A
  card_actor : p ^ 2 ≤ Nat.card A
  finite : Finite G
  invariant : ∀ a : A, a ≠ 1 → ∀ b : A, (θ a).map (α b).toMonoidHom = θ a
  solvable : ∀ a : A, a ≠ 1 → Group.IsSolvable (θ a)
  coprime : ∀ a : A, a ≠ 1 → Nat.Coprime p (Nat.card (θ a))
  le_fixed : ∀ a : A, a ≠ 1 → ∀ g ∈ θ a, α a g = g
  balance : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∀ g ∈ θ a, α b g = g → g ∈ θ b


end CFSG.GroupTheory.SteinbergBS
