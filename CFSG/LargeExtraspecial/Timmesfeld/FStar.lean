module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public section

namespace CFSG.LargeExtraspecial.Timmesfeld

open CFSG.Assembly Subgroup

open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def fStar (M : Subgroup G) : Subgroup G := (CFSG.generalizedFitting M).map M.subtype

@[expose] def IsExtraspecial2 (Q : Subgroup G) : Prop :=
  IsPGroup 2 Q ∧ ⁅Q, Q⁆ = (Subgroup.center Q).map Q.subtype ∧ Nat.card (⁅Q, Q⁆ : Subgroup G) = 2

@[expose] def HasWidth (Q : Subgroup G) (n : ℕ) : Prop := Nat.card Q = 2 ^ (2 * n + 1)

@[expose] def Qa (a : G) : Subgroup G := fStar (centralizer ({a} : Set G))

@[expose] def M (z : G) : Subgroup G := centralizer ({z} : Set G)

@[expose] def L (z a : G) : Subgroup G := fStar (M z) ⊔ (Qa a ⊓ M z)

@[expose] def L0 (z a : G) : Subgroup G := Qa a ⊓ M z


namespace Section4


end Section4

namespace Section5


end Section5

namespace Section12


end Section12

end CFSG.LargeExtraspecial.Timmesfeld
