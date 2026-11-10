module

public import Certificates.Kernel.J2Cover.K21
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelJ2Cover

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Child3 CFSG.KC.J2Cover
open CFSG.KC.Misc.ArrEnum CFSG.KC.DecText TxtKernel
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native CFSG.ComponentClassification.J2Cover
open CFSG.ComponentClassification.J2Cover.Kernel

theorem crT_cnt : Nat.beq (prodCnt 315 9 3 CRT.LR CRT.TR (ord4K 315 9)) RT.N = true := by quickRfl

@[expose] noncomputable def fRT (j : Nat) : Bool :=
  repK 315 9 RT.GP RT.GIP 3 RT.CS RT.OFF RT.CI RT.E RT.P RT.L RT.K RT.S RT.SI RT.N 4000 j

#lc_blocks RTB fRT 660 8


end CertificateChecks.KernelJ2Cover

end
