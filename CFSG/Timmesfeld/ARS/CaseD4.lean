module

public import CFSG.Timmesfeld.ARS.CaseD4Frame
public import CFSG.Timmesfeld.ARS.LinearChain
public import CFSG.Timmesfeld.RankTwo.LevisSpin
public import CFSG.Timmesfeld.RankTwo.LeviData
public import CFSG.Timmesfeld.Outcome

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne CFSG.LieType CFSG.LieType.Universal Matrix

namespace CaseD4

theorem commute_of_mem {G : Type*} [Group G] {R : Set (Subgroup G)} {A A₀ : Subgroup G}
    {P Q : Fin 3 → Subgroup G} (hPQ : LeviSL2Cube R A A₀ P Q) {i j : Fin 3} (hij : i ≠ j)
    {x y : G} (hx : x ∈ P i ⊔ Q i) (hy : y ∈ P j ⊔ Q j) : Commute x y :=
  hPQ.commuting i j hij x hx y hy

end CaseD4


end CFSG.Timmesfeld.ARS
