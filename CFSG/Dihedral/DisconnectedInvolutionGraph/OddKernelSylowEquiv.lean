module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.RankOneSylowTransport
public import CFSG.Dihedral.DisconnectedInvolutionGraph.OddKernelTwoInjection

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G K : Type*} [Group G] [Group K] [Finite G]

theorem odd_kernel_sylow_equiv (hom : G →* K) (hsurjective : Function.Surjective hom)
    (hodd : Odd (Nat.card hom.ker)) (sylow : Sylow 2 G) :
    Nonempty ((sylow : Subgroup G) ≃* (sylow.mapSurjective hsurjective : Subgroup K)) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let image := sylow.mapSurjective hsurjective
  let restricted := hom.comp (sylow : Subgroup G).subtype
  let targetHom : (sylow : Subgroup G) →* (image : Subgroup K) :=
    restricted.codRestrict (image : Subgroup K) (by
      intro element
      change hom element.val ∈ (image : Subgroup K)
      rw [show (image : Subgroup K) = (sylow : Subgroup G).map hom from
        Sylow.coe_mapSurjective hsurjective sylow]
      exact Subgroup.mem_map.mpr ⟨element, element.property, rfl⟩)
  have hinjective : Function.Injective targetHom := by
    intro first second hequal
    exact odd_kernel_two_subgroup_injective hom hodd (sylow : Subgroup G)
      sylow.isPGroup' (congrArg Subtype.val hequal)
  have hsurjectiveTarget : Function.Surjective targetHom := by
    intro target
    have hmem : target.val ∈ (sylow : Subgroup G).map hom := by
      rw [← Sylow.coe_mapSurjective hsurjective sylow]
      exact target.property
    obtain ⟨element, helement, hequal⟩ := Subgroup.mem_map.mp hmem
    exact ⟨⟨element, helement⟩, Subtype.ext hequal⟩
  exact ⟨MulEquiv.ofBijective targetHom ⟨hinjective, hsurjectiveTarget⟩⟩


end CFSG.DisconnectedInvolutionGraph.Helpers
