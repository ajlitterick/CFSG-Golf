module

public import Mathlib.NumberTheory.Niven
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_1

public section

namespace CFSG.OddOrderBasics


theorem complex_character_inversion {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = starRingEnd ℂ (ρ.character g) :=
  Section1.representation_character_inv_eq_star_character ρ g

end CFSG.OddOrderBasics
