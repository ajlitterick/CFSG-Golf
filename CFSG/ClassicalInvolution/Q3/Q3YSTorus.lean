module

public import CFSG.ClassicalInvolution.Q3.Q3YSComp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.ClassicalInvolution.Balance
open scoped MatrixGroups commutatorElement

section Torus

variable {K : Type} [Group K] {k : Type*} [Field k] {D : UniversalRootDatum K}
  {x : (Fin D.rank → ℤ) → k → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (RootSystem.ofCartan D.isFiniteType D.divisible)}

def sl2W (t : kˣ) : Matrix.SpecialLinearGroup (Fin 2) k :=
  sl2Upper (t : k) * sl2Lower (-((t⁻¹ : kˣ) : k)) * sl2Upper (t : k)


end Torus

end CFSG.ClassicalInvolution.Q3.Q3YS
