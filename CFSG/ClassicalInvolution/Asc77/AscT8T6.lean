module

public import CFSG.ClassicalInvolution.Asc77.AscT8T5
import CFSG.ClassicalInvolution.Asc77.AscT8T6Eng

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson

namespace T8T

section Sigma

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem sigmaNorm_le_normalizer_alpha [IsSimpleGroup G] (hA : C27_AlphaConst p f)
    (hs : Std8 p f Ω K J S R T W z t) (hdisc : ¬ DConnected Ω)
    (hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) (hE4 : ¬ MuIsoE4 Ω W) :
    sigmaNorm Ω K ≤ Subgroup.normalizer (alphaOf (Subgroup.closure ({t, z} : Set G)) : Set G) := by
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  exact sigmaNorm_le_normalizer_alphaE hΩ.conjInvariant hs.stand.mem hs.hJ hs.hz hs.ht
    (fun hL => alphaOf_eq_of_mem_dComp hA hs hdisc ⟨W, hs.hW.1, hab, hE4⟩ hL)

end Sigma

end T8T

section Main


end Main

end CFSG.ClassicalInvolution.Asc77
