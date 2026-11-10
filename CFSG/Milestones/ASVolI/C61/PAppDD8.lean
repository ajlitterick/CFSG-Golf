module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDD8
public import CFSG.Milestones.ASVolI.C61.PAppDJ
public import CFSG.Milestones.ASVolI.C61.PAppDC61a

public section

namespace CFSG.QuasithinUnique.burnsideC56_P.AppD

open CFSG.QuasithinUnique.AppD

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Delta5 Equiv
open CFSG.QuasithinUnique.burnsideC56_P.AppC
open CFSG.QuasithinUnique.AppC hiding Cfg Cfg.D_le_Q Cfg.Q_comm_U Cfg.Q_eq Cfg.S_le_N_D
  Cfg.UD_unique Cfg.U_comm_D Cfg.U_inf_D Cfg.aU_spec Cfg.blockU_le_baum Cfg.card_Q Cfg.card_U
  Cfg.conj_mem_blockD Cfg.exists_UD Cfg.hL Cfg.hQ Cfg.hQS Cfg.hSH Cfg.hSN Cfg.hU Cfg.hUQ Cfg.hUS
  Cfg.im_le_Dstd Cfg.mem_Q_iff Cfg.mem_Q_of_pf_eq_one Cfg.omegaOneCenter_le_pCoreOf
  Cfg.pf_eq_one_of_mem_Q Mate.B_eq Mate.B_eq_sup Mate.B_le_sup Mate.D_comm_V Mate.D_elem
  Mate.D_inf_conj Mate.D_le_B Mate.D_le_K Mate.D_le_of_isMax Mate.G_spec Mate.J_eq_B Mate.Q_elem
  Mate.Q_isMax Mate.Q_le_B Mate.Qx_isMax Mate.S_le_N_V Mate.V_comm Mate.V_conj Mate.V_elem
  Mate.V_inf_Q_le_U Mate.V_le_B Mate.V_le_S Mate.V_not_le_Q Mate.V_sq Mate.X'_spec Mate.Yv_isMax
  Mate.Yv_le Mate.baumD_eq Mate.card_V Mate.card_eq_Q Mate.card_symm Mate.cent_U_V Mate.conj_K
  Mate.eq_Q_of_type_bot Mate.eq_Yv_of_type_t1 Mate.exists_vud Mate.fixU_le_of_isMax Mate.fix_mem
  Mate.im_V Mate.pf_ne_one Mate.sqSub_D Mate.sqSub_K Mate.type_cases a5_core a5_core_std
  blockD_le_pCoreOf blockQ_comm_pCoreOf blockU_inf_blockD card_im_S exists_mem_thompsonJ_pi_ne_one
  exists_split exists_split' nonempty_cfg pCoreOf_comm_blockU pCoreOf_eq_blockU_sup_blockD
  swapGen_imJ

variable {G : Type} [Group G] [Finite G]

structure GFour {T M H S L : Subgroup G} (C : GCfg T M H S L) (x : G) where
  r : G
  hrS : r ∈ S
  hrB : r ∉ baum S
  v : G
  hv : v ∈ conjR (C.U) x
  hπ : C.P.pf v = swap 0 1

namespace GFour

variable {T M H S L : Subgroup G} {C : GCfg T M H S L} {x : G} (F : GFour C x)

@[expose] def Y : Subgroup G := GYv C.U (blockD S L) F.v

@[expose] def Y' : Subgroup G := conjR F.Y F.r

@[expose] def A4 : Fin 4 → Subgroup G :=
  ![pCoreOf 2 H, conjR (pCoreOf 2 H) x, F.Y, F.Y']


end GFour

namespace GCfg


end GCfg

namespace GMate
open CFSG.QuasithinUnique.AppD.GMate


end GMate

end CFSG.QuasithinUnique.burnsideC56_P.AppD
