module

public import Certificates.Kernel.Misc.RuCoverNet.Checks7295
public import CFSG.Certificates.Kernel.Misc.RuCoverNetSound
public import Certificates.Kernel.Misc.RuCover.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.SzCoverNative
import all CFSG.Sporadic.Recognition.RuMultiplierInputs
import all CFSG.Sporadic.Presentation.RuExactInputs
import all CFSG.LieType.Multipliers.CoverWords
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Rudvalis

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelMisc.RuCoverNet

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Ru.Exact
  CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Tits
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.Tits
  CFSG.Sporadic.Recognition.RuMultiplier CFSG.Sporadic.RuSchreier CFSG.Quasithin.KGC31.RuCover
  CFSG.EvenSporadicStandard.Induction.RuSz CFSG.EvenSporadicStandard.TwoRu.SzCover

local notation "Ψ" j:max => CFSG.KC.YModel.Sch.netPerm 14 16240 (CFSG.KD.RuCoverNet.U j)

theorem cperm_ev {k n : Nat} {U : Nat → Nat} (j : Nat) :
    CFSG.KC.YModel.Sch.cperm k n U (2 * j + 2) = CFSG.KC.YModel.Sch.netPerm k n (U j) := by
  have h1 : (2 * j + 2).testBit 0 = false := by
    rw [Nat.testBit_zero]
    exact decide_eq_false (by omega)
  have h2 : (2 * j + 2) >>> 1 - 1 = j := by
    rw [Nat.shiftRight_eq_div_pow, Nat.pow_one]
    omega
  unfold CFSG.KC.YModel.Sch.cperm
  rw [h1, h2]
  simp


theorem cpermL_cons {k n : Nat} {U : Nat → Nat} (x : Nat) (cs : List Nat) :
    CFSG.KC.YModel.Sch.cpermL k n U (x :: cs) =
      CFSG.KC.YModel.Sch.cperm k n U x * CFSG.KC.YModel.Sch.cpermL k n U cs := by
  unfold CFSG.KC.YModel.Sch.cpermL
  rw [List.map_cons, List.prod_cons]

theorem cpermL_nil {k n : Nat} {U : Nat → Nat} : CFSG.KC.YModel.Sch.cpermL k n U [] = 1 := rfl

theorem hlet : ∀ g < 3, CFSG.KC.YModel.letOK 14 16240
    (CFSG.KC.Misc.RuCoverNet.F CFSG.KAct.RuRho.A (Nat.add (Nat.mul 2 g) 1))
    (CFSG.KD.RuCoverNet.U g) = true := by
  intro g hg
  interval_cases g
  exacts [CFSG.KD.RuCoverNet.ch7295l0, CFSG.KD.RuCoverNet.ch7295l1, CFSG.KD.RuCoverNet.ch7295l2]

theorem hwords : ∀ i < 17, CFSG.KC.YModel.wordOK 14 6 3 CFSG.KD.RuCoverNet.U
    CFSG.KD.RuCoverNet.GP CFSG.KD.RuCoverNet.GL i = true := by
  intro i hi
  interval_cases i
  exacts [CFSG.KD.RuCoverNet.ch7295w0, CFSG.KD.RuCoverNet.ch7295w1, CFSG.KD.RuCoverNet.ch7295w2,
    CFSG.KD.RuCoverNet.ch7295w3, CFSG.KD.RuCoverNet.ch7295w4, CFSG.KD.RuCoverNet.ch7295w5,
    CFSG.KD.RuCoverNet.ch7295w6, CFSG.KD.RuCoverNet.ch7295w7, CFSG.KD.RuCoverNet.ch7295w8,
    CFSG.KD.RuCoverNet.ch7295w9, CFSG.KD.RuCoverNet.ch7295w10, CFSG.KD.RuCoverNet.ch7295w11,
    CFSG.KD.RuCoverNet.ch7295w12, CFSG.KD.RuCoverNet.ch7295w13, CFSG.KD.RuCoverNet.ch7295w14,
    CFSG.KD.RuCoverNet.ch7295w15, CFSG.KD.RuCoverNet.ch7295w16]


theorem psi_letter (hRho : ruRhoCheck = true) : ∀ g < 3,
    CFSG.KC.YModel.Sch.Good 14 16240 (CFSG.KD.RuCoverNet.U g) ∧ Ψ g = ruRhoGen g := by
  obtain ⟨σ, hσ, hgen⟩ := CertificateChecks.KernelMisc.RuCover.rep_A hRho
  intro g hg
  obtain ⟨h1, h2⟩ := CFSG.KC.Misc.RuCoverNet.letter_perm hσ hlet ⟨g, hg⟩
  exact ⟨h1, h2.trans (hgen ⟨g, hg⟩).symm⟩

theorem psi_chain (hRho : ruRhoCheck = true) : ∀ j < 20,
    CFSG.KC.YModel.Sch.Good 14 16240 (CFSG.KD.RuCoverNet.U j) ∧
      ∀ i, j = 3 + i → Ψ j = CFSG.KC.YModel.Sch.cpermL 14 16240 CFSG.KD.RuCoverNet.U
        (CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP i) (CFSG.KD.RuCoverNet.GL i)) :=
  CFSG.KC.Misc.RuCoverNet.chain_spec (E := 17) (by norm_num) (by norm_num)
    (fun c hc => (psi_letter hRho c hc).1) hwords

theorem psi_good (hRho : ruRhoCheck = true) {j : Nat} (hj : j < 20) :
    CFSG.KC.YModel.Sch.Good 14 16240 (CFSG.KD.RuCoverNet.U j) := (psi_chain hRho j hj).1

theorem psi_val (hRho : ruRhoCheck = true) {i : Nat} (hi : i < 17) {cs : List Nat}
    (hc : CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP i) (CFSG.KD.RuCoverNet.GL i) = cs) :
    Ψ (3 + i) = CFSG.KC.YModel.Sch.cpermL 14 16240 CFSG.KD.RuCoverNet.U cs := by
  rw [← hc]
  exact (psi_chain hRho (3 + i) (by omega)).2 i rfl


theorem codes_rows :
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 2) (CFSG.KD.RuCoverNet.GL 2) = [8, 10] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 3) (CFSG.KD.RuCoverNet.GL 3) = [12, 10] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 4) (CFSG.KD.RuCoverNet.GL 4) = [12, 14] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 5) (CFSG.KD.RuCoverNet.GL 5) = [12, 16] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 6) (CFSG.KD.RuCoverNet.GL 6) = [18, 16] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 7) (CFSG.KD.RuCoverNet.GL 7) =
      [20, 20, 20, 20, 20] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 8) (CFSG.KD.RuCoverNet.GL 8) =
      [16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 9) (CFSG.KD.RuCoverNet.GL 9) = [12, 24] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 10) (CFSG.KD.RuCoverNet.GL 10) = [27] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 11) (CFSG.KD.RuCoverNet.GL 11) = [28, 22] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 12) (CFSG.KD.RuCoverNet.GL 12) = [30, 26] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 13) (CFSG.KD.RuCoverNet.GL 13) =
      [32, 32, 8, 32] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 14) (CFSG.KD.RuCoverNet.GL 14) =
      [32, 8, 32, 32] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 15) (CFSG.KD.RuCoverNet.GL 15) =
      [36, 34, 8, 36, 34, 8] ∧
    CFSG.KC.YModel.Sch.codesL 6 (CFSG.KD.RuCoverNet.GP 16) (CFSG.KD.RuCoverNet.GL 16) =
      [34, 8, 34, 36, 34, 8, 34, 8, 34, 8, 8] := by
  decide +kernel


section Main


theorem hRho : ruRhoCheck = true := Certificates.certificate15025

theorem hS : ∀ j < 3, Rep 16240 ruRhoArrs[j]! (Ψ j) ∧
    (ruRhoArrs.map (invCand 16240))[j]! = invCand 16240 ruRhoArrs[j]! := by
  intro j hj
  have hs : ruRhoArrs.size = 3 := rfl
  refine ⟨?_, getElem!_map_of_lt (by omega)⟩
  rw [(psi_letter hRho j hj).2]
  exact rep_of_allPermsOK (rho_facts hRho).1 (by omega)


theorem e5 : Ψ 5 = Ψ 3 * Ψ 4 := by
  have h := psi_val hRho (i := 2) (by norm_num) codes_rows.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 3, cperm_ev 4] at h
  exact h

theorem e6 : Ψ 6 = Ψ 5 * Ψ 4 := by
  have h := psi_val hRho (i := 3) (by norm_num) codes_rows.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 5, cperm_ev 4] at h
  exact h

theorem e7 : Ψ 7 = Ψ 5 * Ψ 6 := by
  have h := psi_val hRho (i := 4) (by norm_num) codes_rows.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 5, cperm_ev 6] at h
  exact h

theorem e8 : Ψ 8 = Ψ 5 * Ψ 7 := by
  have h := psi_val hRho (i := 5) (by norm_num) codes_rows.2.2.2.1
  rw [cpermL_cons, cpermL_cons, cpermL_nil, mul_one, cperm_ev 5, cperm_ev 7] at h
  exact h


end Main

end CertificateChecks.KernelMisc.RuCoverNet

end
