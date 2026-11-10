module

public import CFSG.Milestones.ASVolI.C121.P4GrpA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {Ω : Type} [Group Ω] [Finite Ω]


namespace burnsideC121_p4_Hyp

variable {X L T R V Y : Subgroup Ω} (h : burnsideC121_p4_Hyp X L T R V Y)
include h


theorem H_le_X : (baum T ⊔ pCoreOf 2 X) ⊔ Y ≤ X := sup_le (sup_le h.S_le_X h.Q_le_X) h.hYX

theorem H_le_NV : (baum T ⊔ pCoreOf 2 X) ⊔ Y ≤ Subgroup.normalizer (V : Set Ω) :=
  h.H_le_X.trans h.X_le_NV


theorem autI_H : autI h.hV ((baum T ⊔ pCoreOf 2 X) ⊔ Y) = autI h.hV (Y ⊔ thompsonJ R) := by
  have hSN := h.S_le_X.trans h.X_le_NV
  have hQN := h.Q_le_X.trans h.X_le_NV
  have hYN := h.hYX.trans h.X_le_NV
  have hJN := h.J_le_X.trans h.X_le_NV
  rw [autI_sup h.hV (sup_le hSN hQN) hYN, autI_sup h.hV hSN hQN,
    autI_eq_bot_of_le_centralizer h.hV h.Q_le_CV, sup_bot_eq, autI_eq_autOn, h.autOn_baum,
    ← autI_eq_autOn h.hV, autI_sup h.hV hYN hJN, sup_comm]


end burnsideC121_p4_Hyp

end CFSG.Quasithin
