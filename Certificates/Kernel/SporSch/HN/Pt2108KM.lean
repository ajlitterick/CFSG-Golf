module

public import Certificates.Kernel.SporSch.HN.Pt2108Defs
public import Certificates.Kernel.LocalQT.Tc.Gen
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelSporSch.HNPt2108

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX CFSG.KC.LL.HNXT4 CFSG.KC.LL.HNXSyl CFSG.KS.EnumBase
open CFSG.KD.HNPt2108 CFSG.Sporadic.HNSchreier CFSG.KD.LgHNX

theorem g_ok : bAnd(allN 5 (fun j => Nat.beq (GMf j) (liftM FAData.pLift[j]!)),
    Nat.beq (GMf 5) (wordC CFSG.KD.HNPt.R (FAData.pKernel.map scodeK))) = true := by quickRfl


end CertificateChecks.KernelSporSch.HNPt2108

set_option Elab.async false

#kqb_range CertificateChecks.KernelSporSch.HNPt2108.pK CertificateChecks.KernelSporSch.HNPt2108.pS 0 90
#kqb_all CertificateChecks.KernelSporSch.HNPt2108.pK CertificateChecks.KernelSporSch.HNPt2108.pS 90
#kqb_range CertificateChecks.KernelSporSch.HNPt2108.qK CertificateChecks.KernelSporSch.HNPt2108.qS 0 27
#kqb_all CertificateChecks.KernelSporSch.HNPt2108.qK CertificateChecks.KernelSporSch.HNPt2108.qS 27
#kqb_range CertificateChecks.KernelSporSch.HNPt2108.rK CertificateChecks.KernelSporSch.HNPt2108.rS 0 6
#kqb_all CertificateChecks.KernelSporSch.HNPt2108.rK CertificateChecks.KernelSporSch.HNPt2108.rS 6

end
