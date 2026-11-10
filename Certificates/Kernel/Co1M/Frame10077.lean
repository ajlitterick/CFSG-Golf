module

public import Certificates.Kernel.Co1M.Base10077
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1M CFSG.KD.Co1M CFSG.KD.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.TreeK

theorem fr77_sym : symK AP77 = true := by quickRfl

theorem fr77_dist_chk : distFK AP77 om77 = true := by quickRfl


theorem ind77_n1_chk : indK AP77 om77 N1T77 P77n1 = true := by quickRfl

theorem ind77_n2_chk : indK AP77 om77 N2T77 P77n2 = true := by quickRfl

theorem ind77_sB_chk : indK AP77 om77 SBT77 P77sB = true := by quickRfl

theorem ind77_e0_chk : ind1K AP77 om77 (getL 0 ET77 0) = true := by quickRfl

theorem ind77_e1_chk : ind1K AP77 om77 (getL 0 ET77 1) = true := by quickRfl

theorem ind77_e2_chk : ind1K AP77 om77 (getL 0 ET77 2) = true := by quickRfl

theorem ind77_e3_chk : ind1K AP77 om77 (getL 0 ET77 3) = true := by quickRfl

theorem ind77_e4_chk : ind1K AP77 om77 (getL 0 ET77 4) = true := by quickRfl


theorem e77_conj_chk : distinctK 5 (conjK EM77 SBK) = true := by quickRfl

theorem e77_invs_chk : invsK EM77 = true := by quickRfl


theorem e77_len : (prodsK EM77 5).length = 32 := Nat.eq_of_beq_eq_true (by quickRfl)

end CertificateChecks.KernelCo1M

end
