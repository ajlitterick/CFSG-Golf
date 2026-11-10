module

public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineHexagonAction
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineHexagonPoints

public section

namespace CFSG.LinearGroups.UnitaryThreeOverNine

open Matrix CFSG.Assembly.LowTwoRank

theorem hexagon_facts {F : Type} [Field F] (hF : Nat.card F = 9) :
    (incGraph F).Connected ∧ (incGraph F).girth = 12 ∧ (incGraph F).diam = 6 ∧
    (pointGraph F).Connected ∧ (pointGraph F).diam = 3 ∧
    (∀ (p : NonisoLine F) (k : Fin 4),
      {q : NonisoLine F | (pointGraph F).dist p q = k}.ncard = ![1, 6, 24, 32] k) ∧
    (∀ (p : NonisoLine F) (T : HexLine F), ∃! q : NonisoLine F, q ∈ T.1 ∧
      ∀ q' ∈ T.1, (pointGraph F).dist p q ≤ (pointGraph F).dist p q') := by
  obtain ⟨-, hconn, hgirth, hdiam, hΓconn, hΓdiam, hlayer, hnear⟩ := (hexagonData hF).hexagon
  exact ⟨hconn, hgirth, hdiam, hΓconn, hΓdiam, hlayer, hnear⟩


end CFSG.LinearGroups.UnitaryThreeOverNine
