module

public import CFSG.Milestones.ASVolI.H6
public import CFSG.Quasithin.AppendixH.H12.Vocab

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH

@[expose] def FormClause {G : Type*} [Group G] {V : Type*} [CommGroup V] {K : Type*} [Field K]
    (ρ : G →* MulAut V) (L : Subgroup G) (ι : K →+* AddMonoid.End (Additive V))
    (f : V → V → K) : Prop :=
  IsUnitaryForm ι f ∧
    (∀ g ∈ L, (∀ (c : K) (v : V), ρ g (kSmul ι c v) = kSmul ι c (ρ g v)) ∧
      ∀ u v : V, f (ρ g u) (ρ g v) = f u v) ∧
    (∃ q : V → ZMod 2, IsQuadFormOn q ∧ (∀ u : V, f u u = 0 ∨ f u u = 1) ∧
      (∀ u : V, q u = 0 ↔ f u u = 0) ∧ ∀ g ∈ L, ∀ u : V, q (ρ g u) = q u)


end CFSG.Quasithin.AppendixH.H12
