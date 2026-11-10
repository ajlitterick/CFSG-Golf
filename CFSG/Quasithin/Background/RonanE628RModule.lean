module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.Quasithin.RonanE628

@[expose] def a5GoodAt (p : Fin 5) (w : Fin 5 → ZMod 2) : Prop :=
  ∃ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 ∧ σ ≠ 1 ∧ σ p ≠ p ∧ (fun i => w (σ i)) = w

@[expose] def a5BadAt (p : Fin 5) (w : Fin 5 → ZMod 2) : Prop :=
  (∃ i : Fin 5, i ≠ p ∧ w = fun j => if j = i ∨ j = p then 1 else 0) ∨
    w = fun j => if j = p then 0 else 1

instance (p : Fin 5) (w : Fin 5 → ZMod 2) : Decidable (a5GoodAt p w) :=
  inferInstanceAs (Decidable (∃ σ : Equiv.Perm (Fin 5), σ ^ 3 = 1 ∧ σ ≠ 1 ∧ σ p ≠ p ∧
    (fun i => w (σ i)) = w))

instance (p : Fin 5) (w : Fin 5 → ZMod 2) : Decidable (a5BadAt p w) :=
  inferInstanceAs (Decidable ((∃ i : Fin 5, i ≠ p ∧ w = fun j => if j = i ∨ j = p then 1 else 0) ∨
    w = fun j => if j = p then 0 else 1))


end CFSG.Quasithin.RonanE628
