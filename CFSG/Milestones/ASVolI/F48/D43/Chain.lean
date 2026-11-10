module

public import CFSG.Perm.ChainByOrder
public import CFSG.Certificates.Kernel.RouteP.TabComplete
public import Certificates.Certificate7802

public section

namespace CFSG.ASVolI

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm
  CFSG.Perm.Native

attribute [local irreducible] burnsideF48d_KeysHex burnsideF48d_TabsHex burnsideF48d_GensHex
  burnsideF48d_PhiHex burnsideF48d_limbs burnsideF48d_colTab

instance burnsideF48d_finite_X : Finite ↥burnsideF48d_X := Subgroup.instFiniteSubtypeMem _

section Chains


variable {C : List (Fin 26572 × Finset (Fin 17) × ℕ)}


end Chains


section Reps


instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩


end Reps

section ChainX


end ChainX

section Equiv


end Equiv

end CFSG.ASVolI
