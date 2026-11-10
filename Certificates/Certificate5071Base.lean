
module

public import CFSG.GH74.GLS.C3.Layer2.L5C9Inputs
import CFSG.GH74.GLS.C3.Layer2.L5C9Base
import CFSG.Certificates.Kernel.L5.HFCIdx
import Certificates.Kernel.L5.HFChecks
import CFSG.Certificates.Kernel.L5.HFQSound
import CFSG.Certificates.Kernel.L5.HFPSound
import CFSG.Certificates.Kernel.L5.HFVSound
import Certificates.Kernel.L5.HFRChecks
public import Certificates.Data.Kernel.PermCent.CV

@[expose] public section

open Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.C3.Layer2.L5
  CFSG.GH74.GLS.C3.Layer2.L5.HF CFSG.Certificates.Kernel.PkCV CFSG.Certificates.Kernel.L5H

namespace CertificateChecks.Batch5071

set_option maxRecDepth 100000

private theorem fam0_card_0 : fam0.card = 4 := by decide +kernel

private theorem fam1_card_1 : fam1.card = 4 := by decide +kernel

private theorem one_mem_n24L_2 : (1 : Perm (Fin 16)) ∈ n24L := by decide +kernel

private theorem n24L_mul_chk_3 : mulClosedChkP n24L = true := by
  rw [← map_cOf_ev n24L, mulClosedChkP_map_ev]
  decide +kernel

private theorem n24L_inv_chk_4 : invClosedChkP n24L = true := by
  rw [← map_cOf_ev n24L, invClosedChkP_map_ev]
  decide +kernel

private theorem n24L_nodup_5 : n24L.Nodup := by
  rw [← map_cOf_ev n24L, nodup_map_ev]
  decide +kernel


private theorem wHat_mem_n24L_13 : wHat ∈ n24L := by decide +kernel


private theorem d8L_sub_n24L_chk_15 : d8L.all (fun d => decide (d ∈ n24L)) = true := by
  decide +kernel

private theorem v4L_sub_d8L_chk_16 : v4L.all (fun v => decide (v ∈ d8L)) = true := by
  decide +kernel

private theorem v4L_normal_chk_17 :
    n24L.all (fun m => v4L.all fun v => decide (m * v * m⁻¹ ∈ v4L)) = true := by
  decide +kernel

private theorem cHat_v4L_chk_18 : v4L.all (fun v => decide (cHat * v * cHat⁻¹ ∈ v4L)) = true := by
  decide +kernel


private theorem n24_enum_29 : allQ2 gN n24Entry = true := by
  rw [allQ2_eq]
  simp only [n24Entry_ev G72TabK G72K]
  obtain ⟨hG, hM⟩ := g72Pin G72PinK
  have hc : n24EntryV g72GN g72MP = n24EntryC :=
    funext fun x => by rw [n24EntryV_eq, hG, hM, n24EntryN_eq]
  have e : ∀ k, CFSG.Certificates.Kernel.L5Q.c5071n24Row k =
      CFSG.Certificates.Kernel.L5Q.rowQ gN n24EntryC k := fun _ => by rw [← hc]; rfl
  refine allQ2C_of_rows _ _ fun k hk => CFSG.Certificates.Kernel.L5Q.rowQ_sound ?_
  rw [← e]
  interval_cases k
  exacts [CFSG.Certificates.Kernel.L5Q.c5071n24Row0, CFSG.Certificates.Kernel.L5Q.c5071n24Row1,
    CFSG.Certificates.Kernel.L5Q.c5071n24Row2, CFSG.Certificates.Kernel.L5Q.c5071n24Row3]


private theorem Qpl_mem_fam0_36 : Qpl ∈ fam0 := by decide +kernel

private theorem Qpl_mem_fam1_37 : Qpl ∈ fam1 := by decide +kernel

private theorem G72L_length_38 : G72L.length = 72 := by
  rw [G72L_eq, List.length_map]
  exact (G72tab_facts G72TabK).1

private theorem G72L_nodup_39 : G72L.Nodup := by
  rw [G72L_eq, nodup_map_ev]
  exact (G72tab_facts G72TabK).2.1

private theorem one_mem_G72L_40 : (1 : Perm (Fin 16)) ∈ G72L := by
  rw [G72L_eq, one_eq_ev, mem_map_ev]
  exact (G72tab_facts G72TabK).2.2.1

private theorem G72L_mul_chk_41 : mulClosedChkP G72L = true := by
  rw [G72L_eq, mulClosedChkP_map_ev]
  exact G72C_mul G72TabK

private theorem G72L_inv_chk_42 : invClosedChkP G72L = true := by
  rw [G72L_eq, invClosedChkP_map_ev]
  exact (G72chk_facts G72K).1

private theorem G72L_facts_43 : G72L.all (fun m => linChk m && fam0Chk m) = true := by
  rw [G72L_eq, List.all_map]
  simp only [Function.comp_def, linChk_ev, fam0Chk_ev]
  exact G72LinK

private theorem fam_enum_44 : allQ2 gFam (famEntry G72L) = true := by
  rw [allQ2_eq]
  simp only [famEntry_eq G72TabK G72K]
  obtain ⟨hG, hM⟩ := g72Pin G72PinK
  have hc : famEntryN g72GN g72MP = famEntryC := funext fun x => by rw [hG, hM, famEntryN_eq]
  have e : ∀ k, CFSG.Certificates.Kernel.L5Q.c5071famRow k =
      CFSG.Certificates.Kernel.L5Q.rowQ gFam famEntryC k := fun _ => by rw [← hc]; rfl
  refine allQ2C_of_rows _ _ fun k hk => CFSG.Certificates.Kernel.L5Q.rowQ_sound ?_
  rw [← e]
  interval_cases k
  exacts [CFSG.Certificates.Kernel.L5Q.c5071famRow0, CFSG.Certificates.Kernel.L5Q.c5071famRow1,
    CFSG.Certificates.Kernel.L5Q.c5071famRow2, CFSG.Certificates.Kernel.L5Q.c5071famRow3]


private theorem n24g_mem_47 : n24L.getD 6 1 ∈ n24L := by decide +kernel

private theorem yHat_ne_one_48 : yHat ≠ 1 := by decide +kernel

private theorem d8_enum_49 : n24L.all (fun b => n24L.all fun c => d8Chk b c) = true :=
  d8_enum_of n24TabK d8K

end CertificateChecks.Batch5071

namespace Certificates

end Certificates
