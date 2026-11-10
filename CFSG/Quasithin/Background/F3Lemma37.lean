module

public import CFSG.Quasithin.Background.F3Polygon
public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin

universe u

variable {V : Type u} {Γ : SimpleGraph V} {H : Type*} [Group H] [MulAction H V] [GraphAction H Γ]

namespace Lemma37

variable (s t : H) (x l c : V)

@[expose] def base (i : ℤ) : V :=
  if i = 0 then x else if i = 1 then l else if i = 2 then t • x else t • c


variable {s t x l c}

theorem exists_block (k : ℤ) :
    ∃ j : ℤ, k = 4 * j ∨ k = 4 * j + 1 ∨ k = 4 * j + 2 ∨ k = 4 * j + 3 :=
  ⟨k / 4, by omega⟩


end Lemma37

end CFSG.Quasithin
