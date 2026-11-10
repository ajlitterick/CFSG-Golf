module

public import CFSG.Certificates.Kernel.Census.XsProof

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum CFSG.Monster.B.Co2.Native

theorem validA_unpackP_proved {n w P : Nat} (_hn : n < 2 ^ 32) (hw : n ≤ 2 ^ w)
    (hc : canon1 n w P = true) (hv : pvalid n w P = true) :
    CFSG.RankThree.Native.validA n (unpackP n w P) = true := by
  rw [SP.validA_unpack hw hc]
  exact hv

theorem unpackP_pid_proved {n w : Nat} (hn24 : n ≤ 2 ^ 24) (hw : n ≤ 2 ^ w) :
    unpackP n w (pid n w) = idA n ∧ canon1 n w (pid n w) = true :=
  SP.pid_good_of_le hn24 hw


end CFSG.KC.Census

end
