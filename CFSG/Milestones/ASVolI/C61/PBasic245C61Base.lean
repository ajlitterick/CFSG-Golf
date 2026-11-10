module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Basic245C61Base
public import CFSG.Milestones.ASVolI.C61.PBasic245Single

public section

namespace CFSG.QuasithinUnique.burnsideC56_P

open CFSG.Open CFSG.Quasithin Subgroup

namespace C56
open CFSG.QuasithinUnique.C56

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G}

theorem pCoreOf_ne_bot (hcs : burnsideC56_CS G T M H S L) : pCoreOf 2 H ≠ ⊥ := fun h =>
  blockU_ne_bot (isShort hcs) (le_bot_iff.mp (h ▸ blockU_le_pCoreOf_general hcs))


end C56

end CFSG.QuasithinUnique.burnsideC56_P
