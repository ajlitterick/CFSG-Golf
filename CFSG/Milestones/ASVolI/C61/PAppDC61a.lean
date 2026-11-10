module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppDC61a
public import CFSG.Milestones.ASVolI.C61.PAppDCls3
public import CFSG.Milestones.ASVolI.C61.PBasic245C61Base

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

namespace GCfg

variable {T M H S L : Subgroup G} (C : GCfg T M H S L)
include C

theorem exists_r : ∃ r ∈ S, r ∉ baum S := by
  obtain ⟨σ, hσD, hσE⟩ := exists_dset_not_eset
  have hσ : σ ∈ C.P.im S := by rw [C.hS]; exact (mem_Dstd σ).2 hσD
  obtain ⟨r, hrS, hrσ⟩ := (C.P.mem_im_pf le_rfl).1 hσ
  refine ⟨r, hrS, fun hrB => hσE ?_⟩
  have : C.P.pf r ∈ C.P.im (baum S) :=
    (C.P.mem_im_pf (inf_le_left)).2 ⟨r, hrB, rfl⟩
  rw [C.hB, hrσ] at this
  exact (mem_Estd σ).1 this

theorem mem_im_conj_inv {r : G} (hrS : r ∈ S) {A : Subgroup G} (hAS : A ≤ S)
    {g : Perm (Fin 5)} :
    g ∈ C.P.im (conjSubgroup A r⁻¹) ↔ (C.P.pf r)⁻¹ * g * C.P.pf r ∈ C.P.im A := by
  have hrN : r ∈ S := hrS
  have hrNS : r⁻¹ ∈ Subgroup.normalizer (S : Set G) := inv_mem (Subgroup.le_normalizer hrS)
  have hA'S : conjSubgroup A r⁻¹ ≤ S := by
    have := C5.conjSubgroup_mono hAS r⁻¹
    rwa [C5.conjSubgroup_eq_self hrNS] at this
  have hAN : A ≤ S := hAS
  have hA'N : conjSubgroup A r⁻¹ ≤ S := hA'S
  constructor
  · intro hg
    obtain ⟨y, hy, rfl⟩ := (C.P.mem_im_pf hA'N).1 hg
    have hy' : r⁻¹ * y * r ∈ A := by
      have := mem_conjSubgroup_iff.1 hy
      simpa using this
    have hyN : y ∈ S := hA'N hy
    have hb : C.P.pf (r⁻¹ * y * r) = (C.P.pf r)⁻¹ * C.P.pf y * C.P.pf r := by
      rw [C.P.pf_mul (mul_mem (inv_mem hrN) hyN) hrN, C.P.pf_mul (inv_mem hrN) hyN,
        C.P.pf_inv hrN]
    rw [← hb]
    exact (C.P.mem_im_pf hAN).2 ⟨_, hy', rfl⟩
  · intro hg
    obtain ⟨b, hbA, hbp⟩ := (C.P.mem_im_pf hAN).1 hg
    have hbN : b ∈ S := hAN hbA
    refine (C.P.mem_im_pf hA'N).2 ⟨r * b * r⁻¹, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      have : r⁻¹ * (r * b * r⁻¹) * r⁻¹⁻¹ = b := by group
      rw [this]; exact hbA
    · rw [C.P.pf_mul (mul_mem hrN hbN) (inv_mem hrN), C.P.pf_mul hrN hbN, C.P.pf_inv hrN, hbp]
      group

end GCfg

namespace GMate
open CFSG.QuasithinUnique.AppD.GMate

variable {T M H S L M₀ : Subgroup G} {x : G} (C : GCfg T M H S L) (m : GMate S T M₀ x)
include C m

theorem pf_r' {r : G} (hrS : r ∈ S) (hrB : r ∉ baum S) :
    (C.P.pf r)⁻¹ * swap 0 1 * C.P.pf r = swap 2 3 ∧
      (C.P.pf r)⁻¹ * swap 2 3 * C.P.pf r = swap 0 1 := by
  have hD : C.P.pf r ∈ Dset := by
    have : C.P.pf r ∈ C.P.im S := (C.P.mem_im_pf le_rfl).2 ⟨r, hrS, rfl⟩
    rw [C.hS] at this
    exact (mem_Dstd _).1 this
  have hnE : C.P.pf r ∉ Eset := fun h => hrB (GMate.mem_B_of_pf (m := m) C hrS h)
  exact conj_swap_of' _ hD hnE

theorem a5_members {r v : G} (hrS : r ∈ S) (hrB : r ∉ baum S) (hv : v ∈ conjR (C.U) x)
    (hπ : C.P.pf v = swap 0 1) (B' : Subgroup G) :
    IsMaxElemAbelian S B' ↔
      B' = pCoreOf 2 H ∨ B' = conjR (pCoreOf 2 H) x ∨ B' = GYv C.U (blockD S L) v ∨
        B' = conjR (GYv C.U (blockD S L) v) r := by
  obtain ⟨hYmax, -⟩ := GMate.Yv_isMax (m := m) C hv hπ
  obtain ⟨hσ1, hσ2⟩ := GMate.pf_r' (m := m) C hrS hrB
  constructor
  · intro hB'
    rcases GMate.type_cases (m := m) C hB' with h | h | h | h
    · exact Or.inl (GMate.eq_Q_of_type_bot (m := m) C hB' h)
    · exact Or.inr (Or.inr (Or.inl (GMate.eq_Yv_of_type_t1 (m := m) C hB' h hv hπ)))
    · refine Or.inr (Or.inr (Or.inr ?_))
      have hrNS : r⁻¹ ∈ Subgroup.normalizer (S : Set G) := inv_mem (Subgroup.le_normalizer hrS)
      have hA' : IsMaxElemAbelian S (conjSubgroup B' r⁻¹) :=
        C56.isMaxElemAbelian_conjSubgroup hB' hrNS
      have hty' : ∀ g, g ∈ C.P.im (conjSubgroup B' r⁻¹) ↔ g = 1 ∨ g = swap 0 1 := by
        intro g
        rw [C.mem_im_conj_inv hrS hB'.1, h]
        constructor
        · rintro (h1 | h1)
          · left
            have : g = C.P.pf r * 1 * (C.P.pf r)⁻¹ := by
              calc g = C.P.pf r * ((C.P.pf r)⁻¹ * g * C.P.pf r) * (C.P.pf r)⁻¹ := by group
                _ = _ := by rw [h1]
            rw [this]; group
          · right
            have e2 : swap (0 : Fin 5) 1 = C.P.pf r * swap 2 3 * (C.P.pf r)⁻¹ := by
              rw [← hσ1]; group
            calc g = C.P.pf r * ((C.P.pf r)⁻¹ * g * C.P.pf r) * (C.P.pf r)⁻¹ := by group
              _ = _ := by rw [h1, ← e2]
        · rintro (h1 | h1)
          · left; rw [h1]; group
          · right
            rw [h1]; exact hσ1
      have heq := GMate.eq_Yv_of_type_t1 (m := m) C hA' hty' hv hπ
      rw [C56.conjR_eq, ← heq]
      exact (C5.conjSubgroup_inv_conjSubgroup B' r).symm
    · exact Or.inr (Or.inl ((GMate.eq_VD_of_type_E (m := m) C hB' h).trans (GMate.Qx_eq (m := m) C).symm))
  · intro hB'
    rcases hB' with rfl | rfl | rfl | rfl
    · exact GMate.Q_isMax (m := m) C
    · exact GMate.Qx_isMax (m := m) C
    · exact hYmax
    · exact C56.isMaxElemAbelian_conjSubgroup hYmax (Subgroup.le_normalizer hrS)


end GMate

end CFSG.QuasithinUnique.burnsideC56_P.AppD
