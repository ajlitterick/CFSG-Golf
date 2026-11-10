module

public import CFSG.Certificates.Kernel.BabyMonster.TcFive.All
public import CFSG.Certificates.Kernel.BabyMonster.Seeds.Check0
public import Certificates.Kernel.BabyMonster.FiveA.Basic

public section

namespace CertificateChecks.KernelBM.TcFive

open CFSG.KC.BM CFSG.KC.BM.TcFive CertificateChecks.KernelBM.FiveA

set_option maxRecDepth 100000

theorem e_q0 : stripMat E * stripMat Five.W_sq3 = stripMat Five.W_sq3 * stripMat E :=
  (mul1 (C := EQ) wf_E Five.wf_W_sq3 (by bm_strips4 CFSG.KC.BM.TcFive.c_EQ 69)).trans
    (mul1 Five.wf_W_sq3 wf_E (by bm_strips4 CFSG.KC.BM.TcFive.cm_eq0 69)).symm

theorem e_u : stripMat E * stripMat U = stripMat U * stripMat E :=
  (mul1 (C := EU) wf_E wf_U (by bm_strips4 CFSG.KC.BM.TcFive.c_EU 69)).trans
    (mul1 wf_U wf_E (by bm_strips4 CFSG.KC.BM.TcFive.cm_eu 69)).symm

theorem u_eq : stripMat U = stripMat Five.Q2 * stripMat Five.Q3_sq1 * stripMat Five.Q4 *
    stripMat Five.Zp4 := by
  rw [← mul1 wf_v121 Five.wf_Zp4 (by bm_strips4 CFSG.KC.BM.TcFive.c_U 69),
    ← mul1 wf_v120 Five.wf_Q4 (by bm_strips4 CFSG.KC.BM.TcFive.c_v121 69),
    ← mul1 Five.wf_Q2 Five.wf_Q3_sq1 (by bm_strips4 CFSG.KC.BM.TcFive.c_v120 69)]

theorem conj_a : stripMat Seeds.A1 * stripMat G = stripMat G * stripMat AP :=
  (mul1 (C := AG) Seeds.wf_A1 wf_G (by bm_strips4 CFSG.KC.BM.TcFive.c_AG 69)).trans
    (mul1 wf_G wf_AP (by bm_strips4 CFSG.KC.BM.TcFive.conjA 69)).symm

theorem conj_b : stripMat Seeds.A2 * stripMat G = stripMat G * stripMat BP :=
  (mul1 (C := BG) Seeds.wf_A2 wf_G (by bm_strips4 CFSG.KC.BM.TcFive.c_BG 69)).trans
    (mul1 wf_G wf_BP (by bm_strips4 CFSG.KC.BM.TcFive.conjB 69)).symm

theorem conj_i : stripMat G * stripMat Gi = 1 :=
  one1 wf_G wf_Gi (by bm_strips4 CFSG.KC.BM.TcFive.conjI 69)

end CertificateChecks.KernelBM.TcFive

end
