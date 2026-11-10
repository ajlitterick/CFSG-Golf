module

public import CFSG.Quasithin.AppendixH.H12.Basic

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH

structure Trans {Γ : Type*} [Group Γ] (L' : Subgroup Γ) {G : Type*} [Group G] (L : Subgroup G)
    {V' V : Type*} [CommGroup V'] [CommGroup V] (ρ' : Γ →* MulAut V') (ρ : G →* MulAut V) where
  φ : ↥L' ≃* ↥L
  β : V' ≃* V
  compat : ∀ (g : ↥L') (v : V'), ρ (φ g : G) (β v) = β (ρ' (g : Γ) v)

namespace Trans


end Trans

end CFSG.Quasithin.AppendixH.H12
