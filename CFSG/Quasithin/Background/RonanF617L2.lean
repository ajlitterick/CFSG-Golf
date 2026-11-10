module

public import CFSG.Quasithin.Background.RonanF617Setting

public section

namespace CFSG.Quasithin.RonanF617

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.GorensteinWalter
  CFSG.Quasithin CFSG.Quasithin.F6

structure L2 {D : Type} [Group D] [Finite D] (G₁ G₂ K : Subgroup D) (F : Type) [Field F]
    [Finite F] (p f : ℕ) : Prop extends Setting G₁ G₂ K where
  prime : p.Prime
  ne_two : p ≠ 2
  one_le : 1 ≤ f
  five_le : 5 ≤ p ^ f
  mod_eight : p ^ f % 8 = 3 ∨ p ^ f % 8 = 5
  card_field : Nat.card F = p ^ f

namespace Setting


end Setting

namespace L2


end L2

end CFSG.Quasithin.RonanF617
