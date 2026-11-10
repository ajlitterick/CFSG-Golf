module

public import Mathlib.SetTheory.Cardinal.Finite

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

namespace Fintype


end Fintype

namespace One
/--
A finite type with a `1` element has nonzero cardinality.
-/
lemma natCard_ne_zero_of_finite
    (H : Type*) [One H] [Finite H] :
    Nat.card H ≠ 0 := by
  exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩

/--
In characteristic zero, the cardinality of a finite type with a `1` element
is nonzero in any semiring.
-/
lemma natCast_natCard_ne_zero_of_finite
    (H : Type*) [One H] [Finite H]
    (k : Type*) [Semiring k] [CharZero k] :
    (Nat.card H : k) ≠ 0 := by
  intro h
  exact One.natCard_ne_zero_of_finite H (Nat.cast_eq_zero.mp h)

end One
