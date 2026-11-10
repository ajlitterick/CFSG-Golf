module

public import CFSG.Quasithin.Background.HFL3Q

public section

namespace CFSG.Quasithin.H.L3Nine

open Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

theorem pt_mem_blkW (hK : Nat.card K = (2 ^ n) ^ 2) {v : Fin 3 → K} (hv : v 2 = 0) :
    pt hK v ∈ blkW n K := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [mat_pt, rk1_apply, hv]


end CFSG.Quasithin.H.L3Nine
