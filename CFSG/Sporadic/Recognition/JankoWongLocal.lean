module

public import CFSG.Sporadic.Recognition.JankoWongLemma13b

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Subgroup CFSG.GH74 CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]


theorem nonempty_setup_of_doubleCover (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {z : G} (hz : orderOf z = 2) (hH : IsDoubleCoverOfAlt ↥(centralizer ({z} : Set G)) 8) :
    Nonempty (Setup G) := by
  have hz1 : z ≠ 1 := fun e => by
    rw [e, orderOf_one] at hz; exact absurd hz (by norm_num)
  obtain ⟨ρ, hρ⟩ := isCover8_of_isDoubleCoverOfAlt hH (zIn_mem_center z)
    (fun e => hz1 (congrArg Subtype.val e))
  exact ⟨⟨z, ρ, hz, hρ, hs, hnab⟩⟩


end CFSG.Sporadic.Recognition.JankoWong
