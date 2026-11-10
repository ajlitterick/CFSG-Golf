module

public import CFSG.GH74.GLS.C3.Statements
public import CFSG.GH74.GLS.C3.Layer1.P34Stmt

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools

section Vocab

variable {G : Type} [Group G]


structure Setup1D (x : G) (K T : Subgroup G) : Prop where
  sylowT : IsSylowOf 2 T (centralizer ({x} : Set G))
  sylowT0 : IsSylowOf 2 (T ⊓ NxK x K) (NxK x K)

@[expose] def IsFMember (x : G) (K T : Subgroup G) (f : G) : Prop :=
  f ∈ T ∧ orderOf f = 2 ∧ (∀ p ∈ T ⊓ K, f * p = p * f) ∧ f ≠ x ∧
    pLayerOf 2 (K ⊓ centralizer ({f} : Set G)) ≠ ⊥

@[expose] def IsFU2 (x y : G) (K : Subgroup G) (f : G) : Prop :=
  Is2TerminalU2Triple x y K ∧ ∃ T : Subgroup G, Setup1D x K T ∧ IsFMember x K T f

@[expose] def FMax1 (x y : G) (K : Subgroup G) (f : G) : Prop :=
  IsFU2 x y K f ∧ ∀ (x' y' : G) (K' : Subgroup G) (f' : G), IsFU2 x' y' K' f' →
    Nat.card (kBar K') ≤ Nat.card (kBar K)

@[expose] def FMax2 (x y : G) (K : Subgroup G) (f : G) : Prop :=
  FMax1 x y K f ∧ ∀ (x' y' : G) (K' : Subgroup G) (f' : G), FMax1 x' y' K' f' →
    twoPartCard (centralizer ({x'} : Set G)) ≤ twoPartCard (centralizer ({x} : Set G))

@[expose] def FMax3 (x y : G) (K : Subgroup G) (f : G) : Prop :=
  FMax2 x y K f ∧ ∀ (x' y' : G) (K' : Subgroup G) (f' : G), FMax2 x' y' K' f' →
    twoPartCard (centralizer ({f'} : Set G)) ≤ twoPartCard (centralizer ({f} : Set G))

end Vocab


end CFSG.GH74.GLS
