module

public import CFSG.ClassicalInvolution.Balance.FrameIndex.Pairing
public import CFSG.ClassicalInvolution.Balance.WeakFrame.Transvection

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.ClassicalInvolution.Generic
open scoped IsMulCommutative

variable {F : Type*} [Field F] {G : Type*} [Group G]


section Frame

variable {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}

theorem weakPairingAdj_iff [Finite G] (Fr : WeakPreFrame F Ω E S) {K L : Subgroup G}
    (hL : L ∈ S) {z : G} (hz : IsCentralInvolution L z) :
    WeakPairingAdj E K L ↔ z ∉ axisSub E K := by
  constructor
  · rintro ⟨z', hz', h⟩
    rwa [Fr.eq_of_central hL hz hz']
  · exact fun h => ⟨z, hz, h⟩

theorem weak_isMulCommutative (Fr : WeakPreFrame F Ω E S) : IsMulCommutative ↥E :=
  ⟨⟨fun x y => Subtype.ext (Fr.comm x.2 y.2)⟩⟩


section Construction


end Construction


end Frame

end CFSG.ClassicalInvolution.Balance
