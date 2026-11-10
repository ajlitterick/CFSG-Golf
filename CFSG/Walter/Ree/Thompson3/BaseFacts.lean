module

public import CFSG.Walter.Ree.Thompson3.Base

public section

namespace CFSG.Walter.Ree.T2


variable {k : Type} [Field k] [CharP k 3]


namespace RType

variable {σ : k ≃+* k} {d : k}
variable {G : Type} [Group G] [Finite G] (R : RType G k σ d)

theorem K_P0_K : R.K * R.ι (pp σ 0 (-1) 1) * R.K =
    R.ι (tY σ d ^ 2 * ThompsonN.J σ) * R.K * R.ι (pp σ 0 (-1) 1) := by
  have h := R.rel_a
  rw [map_mul, map_pow]
  change R.K * R.ι (pp σ 0 (-1) 1) * R.K = R.ι (tY σ d) ^ 2 * R.Jg * R.K * R.ι (pp σ 0 (-1) 1)
  rw [← h]
  calc R.K * R.ι (pp σ 0 (-1) 1) * R.K = R.K * R.ι (pp σ 0 (-1) 1) * R.K *
        (R.ι (pp σ 0 (-1) 1))⁻¹ * (R.K * R.K) * R.ι (pp σ 0 (-1) 1) := by
          rw [R.K_mul_K]; group
    _ = _ := by group


end RType

end CFSG.Walter.Ree.T2
