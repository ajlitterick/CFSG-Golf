module

public import CFSG.ClassicalInvolution.SmallCases.DisconnectedA2
public import CFSG.ClassicalInvolution.SmallCases.DisconnectedTight
public import CFSG.ClassicalInvolution.TwoGroupCase.TightPair

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}


theorem uniqueInvolutionNormal_of_quaternion_sylow (hz : orderOf z = 2) (hzK : z ∈ K)
    (hKC : K ≤ Subgroup.centralizer ({z} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({z} : Set G))).Normal) (T : Sylow 2 K)
    (hT : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((T : Subgroup K) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    UniqueInvolutionNormal K z :=
  ⟨hz, hzK, (unique_involution_of_quaternion_sylow hzK hz hKC T hT).1, hKC, hKn⟩


end CFSG.ClassicalInvolution
