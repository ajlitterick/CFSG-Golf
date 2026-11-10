module

public import CFSG.ClassicalInvolution.Q3.Q3NFPair
public import CFSG.ClassicalInvolution.Q3.Q3KCGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NF

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3KB
  CFSG.ClassicalInvolution.Q3.Q3KC
open scoped commutatorElement


section Defs

variable {G : Type} [Group G]

structure PairData3 (Φ : Set (Subgroup G)) (A : Subgroup G) (a : G) (K K' : Subgroup G)
    (w w' : G) : Prop where
  memK : K ∈ centralizingMembers Φ {a}
  memK' : K' ∈ centralizingMembers Φ {a}
  clsK : IsClassicalMember3In (centralizingLayer Φ {a}) K w
  clsK' : IsClassicalMember3In (centralizingLayer Φ {a}) K' w'
  memA : w ∈ A
  memA' : w' ∈ A
  sq : w * w = 1
  sq' : w' * w' = 1
  ne_one : w ≠ 1
  ne_one' : w' ≠ 1
  ne : w ≠ w'
  comm : w * w' = w' * w
  central : ∀ x ∈ K, w * x = x * w
  central' : ∀ x ∈ K', w' * x = x * w'
  cross : ∀ x ∈ K', ⁅w, x⁆ ∈ oddCoreIn (centralizingLayer Φ {a})
  cross' : ∀ x ∈ K, ⁅w', x⁆ ∈ oddCoreIn (centralizingLayer Φ {a})

end Defs

section Pair


end Pair

section Triple


end Triple

end CFSG.ClassicalInvolution.Q3.Q3NF
