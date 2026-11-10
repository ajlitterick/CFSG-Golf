module

public import Mathlib.Algebra.Group.Hom.Defs

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3B

@[expose] def nfProd {M : Type*} [Monoid M] (x y : Fin 4 → M) (z : M) (e : List ℕ) : M :=
  x 0 ^ e.getD 0 0 * x 1 ^ e.getD 1 0 * x 2 ^ e.getD 2 0 * x 3 ^ e.getD 3 0 *
    y 0 ^ e.getD 4 0 * y 1 ^ e.getD 5 0 * y 2 ^ e.getD 6 0 * y 3 ^ e.getD 7 0 * z ^ e.getD 8 0


end CFSG.HardMathSupport.Solomon.Coordinator.B3B

end
