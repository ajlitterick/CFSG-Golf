module

public import CFSG.Monster.Existence.Defs
import CFSG.Monster.Existence.Compat.OneStroth
import CFSG.Monster.Existence.MilestoneTableOne
import CFSG.Milestones.CL_LIT_Stroth_Leon_Sims_Baby_Monster_recognition
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

universe u v w

namespace CFSG.Open


end CFSG.Open

namespace CFSG.Open


end CFSG.Open

namespace CFSG.Milestones

open CFSG.Monster.Existence in
theorem cl_lit_monster_existence_griess_conway :
    MonsterExistenceStatement MGriess :=
  monsterExistenceStatement_MGriess_of_recognition fun d₀ hd₀ hrank G _ _ _ d hd hc =>
    cl_lit_stroth_leon_sims_baby_monster_recognition_models d₀ hd₀ hrank G d hd hc

end CFSG.Milestones
