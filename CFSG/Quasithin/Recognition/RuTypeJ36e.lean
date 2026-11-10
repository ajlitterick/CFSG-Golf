module

public import CFSG.Quasithin.Recognition.RuTypeJ36d
public import CFSG.Quasithin.Recognition.RuTypeGL25

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G]


namespace RuDataM

variable (M : RuDataM G) [Finite G]

section Five

variable {M} {b : G} (hbH : b ∈ ruH M.T) (hb5 : orderOf b = 5)
include hbH hb5


theorem comm_V5
    (u v : V5 b) : u * v = v * u := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 5) (G := V5 b)
    (by rw [card_V5 hbH hb5]; norm_num)
  exact h.is_comm.comm u v


end Five

end RuDataM

end CFSG.Quasithin.RuType
