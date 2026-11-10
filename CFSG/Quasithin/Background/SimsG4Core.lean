module

public import CFSG.Quasithin.Background.SimsG4Defs

public section

namespace CFSG.Quasithin.SimsG4

variable {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]

theorem mul_inv_apply (g : V ≃ₗ[F] V) (y : V) : g (g⁻¹ y) = y :=
  congrArg (fun e : V ≃ₗ[F] V => e y) (mul_inv_cancel g)


end CFSG.Quasithin.SimsG4
