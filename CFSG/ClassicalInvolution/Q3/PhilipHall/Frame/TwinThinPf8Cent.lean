module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf7Basic

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

set_option linter.unusedSectionVars false

namespace TwinThin

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S


theorem fam_of_conj_pi {L : Subgroup G} (hL : L ∈ conjSub g '' π) :
    L ∈ fam K (conjSub g (piGen π)) := by
  have hπg := isMaxOrb_conj S.hos.graph S.hπ g
  obtain ⟨a, ha, haL⟩ := transitive_of_maxOrb S.hos.graph hπg K
    (S.hos.mem_conj_image_of_mem S.hπ S.hg) L hL
  have ha' : a ∈ conjSub g (piGen π) := by
    rw [← piGen_conj]; exact ha
  exact ⟨⟨a, ha'⟩, haL⟩


end Setting

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
