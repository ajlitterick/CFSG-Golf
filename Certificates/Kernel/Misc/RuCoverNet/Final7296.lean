module

public import Certificates.Kernel.Misc.RuCoverNet.Final7295
public import Certificates.Kernel.Misc.RuCoverNet.Checks7296E
public import Certificates.Kernel.Misc.RuCoverNet.Checks7296N
public import CFSG.Certificates.Kernel.Misc.RuCoverNetWSound
import CFSG.Certificates.Kernel.Common.ForallTree

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelMisc.RuCoverNet

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Ru.Exact
  CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Tits
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.Tits
  CFSG.Sporadic.Recognition.RuMultiplier CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31.RuCover
  CFSG.EvenSporadicStandard.TwoRu.SzCover CFSG.EvenSporadicStandard.TwoRu.CentCover

local notation "Φ" j:max => CFSG.KC.YModel.Sch.netPerm 14 16240 (CFSG.KD.RuCoverNet7296.V j)
local notation "Ψ" j:max => CFSG.KC.YModel.Sch.netPerm 14 16240 (CFSG.KD.RuCoverNet.U j)

#kc_forall_tree hw7296 (fun i => CFSG.KC.YModel.wordOK 14 6 2 CFSG.KD.RuCoverNet7296.V
  CFSG.KD.RuCoverNet7296.CP CFSG.KD.RuCoverNet7296.CL i = true) 20 CFSG.KD.RuCoverNet7296.ch7296w

#kc_forall_tree hf7296 (fun k => CFSG.KC.Misc.RuCoverNet.eqW CFSG.KD.RuCoverNet7296.V 11 21 0
  (facW k) (jW k) = true) 6 CFSG.KD.RuCoverNet7296.ch7296f

#kc_forall_tree hs7296 (fun i => CFSG.KC.Misc.RuCoverNet.eqW CFSG.KD.RuCoverNet7296.V 11 21 0
  (fW i ++ fW i) [] = true) 6 CFSG.KD.RuCoverNet7296.ch7296s

#kc_forall_tree hc7296 (fun k => CFSG.KC.Misc.RuCoverNet.eqW CFSG.KD.RuCoverNet7296.V 11 21 0
  (fW (k / 6) ++ fW (k % 6)) (fW (k % 6) ++ fW (k / 6)) = true) 36 CFSG.KD.RuCoverNet7296.ch7296c

#kc_forall_tree hm7296 (fun k => CFSG.KC.Misc.RuCoverNet.eqW CFSG.KD.RuCoverNet7296.V 11 21 0
  (CFSG.KC.Misc.RuCoverNet.memW k) (etaW 6 (CFSG.KD.RuCoverNet7296.MC k)) = true) 80
  CFSG.KD.RuCoverNet7296.ch7296m

#kc_forall_tree hy7296 (fun i => CFSG.KC.Misc.RuCoverNet.eqW CFSG.KD.RuCoverNet7296.V 11 21 0
  (jW 4 ++ fW i) (fW i ++ jW 4) = true) 6 CFSG.KD.RuCoverNet7296.ch7296y

#kc_forall_tree hx7296 (fun i => CFSG.KC.Misc.RuCoverNet.eqW CFSG.KD.RuCoverNet7296.V 11 21 0
  (y2W ++ fW i) (fW i ++ y2W) = true) 6 CFSG.KD.RuCoverNet7296.ch7296x

#kc_forall_tree hn7296 (fun c => CFSG.KC.Misc.RuCoverNet.neW CFSG.KD.RuCoverNet7296.V 11 21 0
  (Bool.rec (motive := fun _ => List Int) (etaW 6 c) y5W (Nat.beq c 0)) []
  (CFSG.KD.RuCoverNet7296.NB c) (CFSG.KD.RuCoverNet7296.NX c) (CFSG.KD.RuCoverNet7296.NY c) =
  true) 64 CFSG.KD.RuCoverNet7296.ch7296n

#kc_forall_tree hg7296 (fun k => Bool.rec (motive := fun _ => Bool)
  (CFSG.KC.Misc.RuCoverNet.neW CFSG.KD.RuCoverNet7296.V 11 21 0
    (CFSG.KC.Misc.RuCoverNet.cosU k (CFSG.KD.RuCoverNet7296.KI k))
    (CFSG.KC.Misc.RuCoverNet.cosV k (CFSG.KD.RuCoverNet7296.KI k))
    (CFSG.KD.RuCoverNet7296.KB k) (CFSG.KD.RuCoverNet7296.KX k) (CFSG.KD.RuCoverNet7296.KY k))
  true (Nat.beq (k / 16) (k % 16)) = true) 256 CFSG.KD.RuCoverNet7296.ch7296g


theorem codes7296 :
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 0) (CFSG.KD.RuCoverNet7296.CL 0) = [2, 4] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 1) (CFSG.KD.RuCoverNet7296.CL 1) = [6, 4] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 2) (CFSG.KD.RuCoverNet7296.CL 2) = [6, 8] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 3) (CFSG.KD.RuCoverNet7296.CL 3) = [6, 10] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 4) (CFSG.KD.RuCoverNet7296.CL 4) = [12, 6] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 5) (CFSG.KD.RuCoverNet7296.CL 5) = [14, 8] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 6) (CFSG.KD.RuCoverNet7296.CL 6) = [11] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 7) (CFSG.KD.RuCoverNet7296.CL 7) = [18, 2] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 8) (CFSG.KD.RuCoverNet7296.CL 8) = [20, 10] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 9) (CFSG.KD.RuCoverNet7296.CL 9) = [6, 16] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 10) (CFSG.KD.RuCoverNet7296.CL 10) =
      [24, 24, 24, 24, 24, 24, 24, 24, 24, 24] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 11) (CFSG.KD.RuCoverNet7296.CL 11) =
      [26, 22] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 12) (CFSG.KD.RuCoverNet7296.CL 12) =
      [28, 28, 28, 28, 28, 28] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 13) (CFSG.KD.RuCoverNet7296.CL 13) =
      [14, 14] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 14) (CFSG.KD.RuCoverNet7296.CL 14) = [33] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 15) (CFSG.KD.RuCoverNet7296.CL 15) =
      [34, 22] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 16) (CFSG.KD.RuCoverNet7296.CL 16) =
      [36, 32] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 17) (CFSG.KD.RuCoverNet7296.CL 17) =
      [26, 38] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 18) (CFSG.KD.RuCoverNet7296.CL 18) =
      [40, 40, 40, 40] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP 19) (CFSG.KD.RuCoverNet7296.CL 19) =
      [30, 42] := by
  decide +kernel


section Main


theorem phi_base : ∀ c < 2, CFSG.KC.YModel.Sch.Good 14 16240 (CFSG.KD.RuCoverNet7296.V c) := by
  intro c hc
  interval_cases c
  · exact psi_good hRho (j := 3) (by decide)
  · exact psi_good hRho (j := 4) (by decide)

theorem phi_chain : ∀ j < 22, CFSG.KC.YModel.Sch.Good 14 16240 (CFSG.KD.RuCoverNet7296.V j) ∧
    ∀ i, j = 2 + i → Φ j = CFSG.KC.YModel.Sch.cpermL 14 16240 CFSG.KD.RuCoverNet7296.V
      (CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP i) (CFSG.KD.RuCoverNet7296.CL i)) :=
  CFSG.KC.Misc.RuCoverNet.chain_spec (E := 20) (by decide) (by decide) phi_base hw7296


theorem phi_val {i : Nat} (hi : i < 20) {cs : List Nat}
    (hc : CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet7296.CP i)
      (CFSG.KD.RuCoverNet7296.CL i) = cs) :
    Φ (2 + i) = CFSG.KC.YModel.Sch.cpermL 14 16240 CFSG.KD.RuCoverNet7296.V cs := by
  rw [← hc]
  exact (phi_chain (2 + i) (by omega)).2 i rfl


theorem f2 : Φ 2 = Φ 0 * Φ 1 := by
  have h := phi_val (i := 0) (by decide) codes7296.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 0, cperm_ev 1] at h
  exact h


theorem f4 : Φ 4 = Φ 2 * Φ 3 := by
  have h := phi_val (i := 2) (by decide) codes7296.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 2, cperm_ev 3] at h
  exact h


theorem f9 : Φ 9 = Φ 8 * Φ 0 := by
  have h := phi_val (i := 7) (by decide) codes7296.2.2.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 8, cperm_ev 0] at h
  exact h

theorem f10 : Φ 10 = Φ 9 * Φ 4 := by
  have h := phi_val (i := 8) (by decide) codes7296.2.2.2.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 9, cperm_ev 4] at h
  exact h

theorem f11 : Φ 11 = Φ 2 * Φ 7 := by
  have h := phi_val (i := 9) (by decide) codes7296.2.2.2.2.2.2.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 2, cperm_ev 7] at h
  exact h


section Tables


end Tables


section Fam


end Fam


end Main

end CertificateChecks.KernelMisc.RuCoverNet

end
