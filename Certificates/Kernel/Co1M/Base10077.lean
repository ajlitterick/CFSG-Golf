module

public import Certificates.Kernel.Co1M.Reg10077
public import Certificates.Kernel.Co1M.Data10077
public import Certificates.Kernel.Co1Cover.Data
public import Certificates.Kernel.Co1B.Data2046
public import CFSG.Certificates.Kernel.Co1M.TwoBKSound
public import CFSG.Certificates.Kernel.TreeKSound
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.Co1F2Sound
public import Mathlib.Tactic.NormNum

public section

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1M CFSG.KD.Co1M CFSG.KD.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT
  CertificateChecks.KernelCo1Cover

@[expose] def om77 : Nat := 10075731

@[expose] noncomputable def RB77 : List Nat := R0 :: R1 :: SBK :: RB77T

@[expose] noncomputable def SR77 : List Nat :=
  [getL 0 RB77 33, getL 0 RB77 34, getL 0 RB77 35, getL 0 RB77 36, getL 0 RB77 37, getL 0 RB77 38]

@[expose] noncomputable def YR77 : List Nat := [getL 0 RB77 8, getL 0 RB77 12]

@[expose] noncomputable def PN77 : List Nat := [P77n1, P77n2]

theorem b77_regs : andB (Nat.beq (getL 0 RB77 3) N1) (Nat.beq (getL 0 RB77 4) N2) = true := by
  quickRfl

theorem b77_tr : andB (trEqK N1 N1T77) (andB (trEqK N2 N2T77) (andB (trEqK SBK SBT77)
    (andB (zipK trEqK YR77 YT77) (andB (zipK trEqK SR77 ST77)
      (andB (zipK trEqK EM77 ET77) (zipK trEqK UM77 UT77)))))) = true := by
  quickRfl

theorem b77_e : zipK (ewK [N1, N2]) EW77 EM77 = true := by quickRfl

theorem b77_u : zipK (fun w U => Nat.beq (wK SR77 w) U) SW77 UM77 = true := by quickRfl

theorem b77_perm : andB (permK P77n1 P77n1i) (andB (permK P77n2 P77n2i) (andB (permK P77sB P77sB)
    (andB (permK (getL 0 H77 0) (getL 0 H77i 0)) (andB (permK (getL 0 H77 1) (getL 0 H77i 1))
      (permK WP77 WP77i))))) = true := by
  quickRfl

theorem b77_words : andB (zipK (fun w H => Nat.beq (pwK PN77 w) H) M01W77 H77)
    (andB (zipK (fun w G => Nat.beq (pwK PN77 w) G) M0W77 G77)
      (andB (Nat.beq (pwK PN77 W77) WP77) (Nat.beq (ppc (ppc WP77 P77sB) WP77i) TP77))) = true := by
  quickRfl

theorem b77_fix : andB (allN 2 fun l => andB (Nat.beq (ppg (getL 0 H77 l) 0) 0)
    (Nat.beq (ppg (getL 0 H77 l) 1) 1))
    (andB (allN 3 fun l => Nat.beq (ppg (getL 0 G77 l) 0) 0) (Nat.beq (ppg TP77 0) 1)) = true := by
  quickRfl

theorem b77_gw : andB (Nat.beq (vmF 24 (getL 0 YT77 0) om77) GW77)
    (allN 4 fun l => Nat.beq (vmF 24 (getL 0 UT77 l) GW77) GW77) = true := by
  quickRfl

theorem b77_q : andB (Nat.beq (mulF 24 QP77 QIP77) (idF 24)) (Nat.beq (mulF 24 QIP77 QP77) (idF 24)) =
    true := by
  quickRfl

theorem b77_n12 : getL 0 RB77 3 = N1 ∧ getL 0 RB77 4 = N2 := by
  obtain ⟨h1, h2⟩ := andB_true b77_regs
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2⟩


end CertificateChecks.KernelCo1M

end
