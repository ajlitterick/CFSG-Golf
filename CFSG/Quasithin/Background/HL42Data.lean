module

public meta import Mathlib.Algebra.Field.ZMod
public meta import Mathlib.Data.Matrix.Mul
public meta import Mathlib.Data.Fin.VecNotation
public import Certificates.Certificate7026

public section

namespace CFSG.Quasithin

namespace H

namespace L4

open scoped Matrix


theorem single_mul_self : ∀ i j : Fin 4, i ≠ j →
    (1 + Matrix.single i j (1 : ZMod 2)) * (1 + Matrix.single i j 1) = 1 :=
  Certificates.certificate7026.2.2.2.2.2.2.2.1

theorem single_mulVec_e0 : ∀ i j : Fin 4, j ≠ 0 →
    (1 + Matrix.single i j (1 : ZMod 2)) *ᵥ Pi.single 0 1 = Pi.single 0 1 :=
  Certificates.certificate7026.2.2.2.2.2.2.2.2.1

theorem single_transpose : ∀ i j : Fin 4,
    (1 + Matrix.single i j (1 : ZMod 2))ᵀ = 1 + Matrix.single j i 1 :=
  Certificates.certificate7026.2.2.2.2.2.2.2.2.2.1

theorem eq_zero_of_fix_single : ∀ w : Fin 4 → ZMod 2,
    (∀ i j : Fin 4, j ≠ 0 → i ≠ j → (1 + Matrix.single j i (1 : ZMod 2)) *ᵥ w = w) → w = 0 :=
  Certificates.certificate7026.2.2.2.2.2.2.2.2.2.2

end L4

end H

end CFSG.Quasithin
