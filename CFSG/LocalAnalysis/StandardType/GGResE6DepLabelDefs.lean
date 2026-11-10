module

public import CFSG.LocalAnalysis.StandardType.GGResAssembly

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGA5Label (lab : LargeEvenLabel) : Prop :=
  lab.rank = 5 ∧ ((lab.tag = .A ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1))


@[expose] def GGSchurDvdInput : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (lab : LargeEvenLabel), commutator X = ⊤ →
    LargeEvenInLambda2 lab → (GGE6DepLabel lab ∨ GGA5Label lab) →
    GGHasLabel lab (X ⧸ Subgroup.center X) → Nat.card ↥(Subgroup.center X) ∣ 12

end CFSG.StandardType
