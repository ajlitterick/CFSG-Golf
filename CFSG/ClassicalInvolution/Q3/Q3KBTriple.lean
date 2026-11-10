module

public import CFSG.ClassicalInvolution.Q3.Q3KBSigma
public import CFSG.ClassicalInvolution.Q3.Q3KBLie
public import CFSG.ClassicalInvolution.Q3.Q3KBPair
public import CFSG.ClassicalInvolution.Q3.Q3Y2Lift
public import CFSG.ClassicalInvolution.Q3.Q3YAbs
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3KB

open CFSG.Open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ComponentClassification
open scoped commutatorElement

section Step

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}


end Step

section Pair

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

structure MemberPair (Ω : Set (Subgroup G)) (A K K' : Subgroup G) (w w' : G) : Prop where
  memΩ : K ∈ Ω
  memΩ' : K' ∈ Ω
  le : K ≤ Subgroup.centralizer (A : Set G)
  le' : K' ≤ Subgroup.centralizer (A : Set G)
  mem : w ∈ K
  mem' : w' ∈ K'
  memA : w ∈ A
  memA' : w' ∈ A
  central : ∀ k ∈ K, k * w = w * k
  central' : ∀ k ∈ K', k * w' = w' * k
  comm : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x
  sq : w * w = 1
  sq' : w' * w' = 1
  ne : w ≠ w'
  ne_one : w ≠ 1
  ne_one' : w' ≠ 1


end Pair

section Triple


end Triple

end CFSG.ClassicalInvolution.Q3.Q3KB
