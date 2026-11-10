
module

public import CFSG.Monster.B.Fischer.Fi22OuterBase
import all CFSG.Monster.B.Fischer.Fi22OuterBase

public import CFSG.Monster.B.Fischer.Fi22OuterCheck
import all CFSG.Fischer.F4

public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Fischer

theorem rep_fi22OuterPerm3510 {L : ℕ} (hL : L < 151) :
    Rep 3510 (fi22OuterArr3510 L) (fi22OuterPerm3510 L) :=
  (rep_permOfArr (fi22Outer_check.2.2.2.1 L hL)).1

theorem rep_fi22OuterPerm693 {L : ℕ} (hL : L < 104) :
    Rep 693 (fi22OuterArr693 L) (fi22OuterPerm693 L) :=
  (rep_permOfArr (fi22Outer_check.2.2.2.2.1 L hL)).1


end CFSG.Monster.B.Fischer
