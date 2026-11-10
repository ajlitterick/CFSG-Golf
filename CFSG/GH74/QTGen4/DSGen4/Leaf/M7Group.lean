module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBS3Vertex
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyModel
public import CFSG.GH74.QTGen4.DSGen4.Leaf.FrattiniChief

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open scoped commutatorElement

namespace M7

variable {G : Type} [Group G]

structure Ctx (L P : Subgroup G) (d k t : G) : Prop where
  hLP : L ≤ P
  hPL : P ≤ Subgroup.normalizer (L : Set G)
  hchar : CharTwo P
  hd : d ∈ P
  hd3 : orderOf d = 3
  hdc : ∀ l ∈ L, ⁅d, l⁆ ∈ pCoreOf 2 P
  hk : k ∈ L
  hk3 : orderOf k = 3
  ht : t ∈ L
  ht2 : t ^ 2 ∈ pCoreOf 2 P
  hkt : (t * k)⁻¹ * (k ^ 2 * t) ∈ pCoreOf 2 P
  hgen : ∀ l ∈ L, ∃ i j : ℕ, (t ^ i * k ^ j)⁻¹ * l ∈ pCoreOf 2 P
  hord3 : ∀ x ∈ L, orderOf x = 3 → k⁻¹ * x ∈ pCoreOf 2 P ∨ (k ^ 2)⁻¹ * x ∈ pCoreOf 2 P

variable {L P : Subgroup G} {d k t : G}


@[expose] def Ctx.tP (h : Ctx L P d k t) : ↥P := ⟨t, h.hLP h.ht⟩


end M7

end CFSG.GH74.QTGen4.DSGen4
