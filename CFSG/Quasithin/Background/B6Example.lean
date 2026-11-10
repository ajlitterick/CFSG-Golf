module

public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique

namespace B6


private theorem card_perm_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]


end B6


end CFSG.Quasithin
