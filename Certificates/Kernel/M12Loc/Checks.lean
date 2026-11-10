module

public import Certificates.Data.Kernel.M12Loc
public import Certificates.Kernel.M12Loc.Data

public section

namespace CertificateChecks.KernelM12Loc

open CFSG.KC.M12Loc CFSG.GH74.M12.Hyp CFSG.RankThree.PartTwo.Toolkit.M12

theorem TT_eq : D.TT = trT := by decide +kernel

theorem nz_list : listOK (predP zT) D.TT idxNP D.TNP = true := by decide +kernel

theorem nz_swap : D.TNP.any (fun t => tconj t zT == tpow zT 2) = true := by decide +kernel

theorem count_NP : countOK (predN [xT, yT] P0T) D.TNP 108 = true := by decide +kernel

theorem count_CE : countOK (predC [zT, xT]) D.TNP 9 = true := by decide +kernel

theorem count_CF : countOK (predC [zT, yT]) D.TNP 9 = true := by decide +kernel

theorem count_NA : countOK (predN [zT, aT] AT) D.TNP 54 = true := by decide +kernel

theorem count_CA : countOK (predC [zT, aT]) D.TNP 9 = true := by decide +kernel

theorem np_ok : npOK D.TNP = true := by decide +kernel

theorem center_ok : centerOK = true := by decide +kernel

theorem afix_ok : aFixOK = true := by decide +kernel

theorem na_list : listOK (predP aT) D.TT idxNa D.TNa = true := by decide +kernel

theorem orb_ok : orbOK D.W = true := by decide +kernel

theorem psi_rows_0 : psiRows (D.TNa.take 24) D.TNa = true := by decide +kernel

theorem psi_rows_1 : psiRows ((D.TNa.drop 24).take 24) D.TNa = true := by decide +kernel

theorem psi_rows_2 : psiRows (D.TNa.drop 48) D.TNa = true := by decide +kernel

theorem psi_val : psiValOK D.TNa = true := by decide +kernel


end CertificateChecks.KernelM12Loc

end
