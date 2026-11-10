module

public import CFSG.Quasithin.Background.G1Basic
public import CFSG.Quasithin.Background.G2L2Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.SL2Model CFSG.Quasithin.G1
open scoped MatrixGroups Pointwise commutatorElement

variable {G : Type} [Group G]


namespace L2Setting

variable [Finite G] {n : ℕ} {V V₁ L T H : Subgroup G} (S : L2Setting n V V₁ L T H)

include S

omit [Finite G] in
theorem card_V : Nat.card ↥V = Nat.card (GaloisField 2 n) ^ 2 := by
  have h1 : Nat.card ↥V = Nat.card (Wm (GaloisField 2 n)) := Nat.card_congr S.D.ψ.toEquiv
  have h2 : Nat.card (Wm (GaloisField 2 n)) = Nat.card (Fin 2 → GaloisField 2 n) :=
    Nat.card_congr Multiplicative.toAdd
  rw [h1, h2, Nat.card_fun]
  simp


end L2Setting

end CFSG.Quasithin
