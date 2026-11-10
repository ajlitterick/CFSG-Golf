module

public import CFSG.LieType.Chevalley.RootOps.Cover
public import CFSG.LieType.Chevalley.RootOps.Data.D4Comm

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch45

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem d4_repsCheck : repsCheck .D4 d4Reps = true := by decide +kernel

private theorem d4_coverCheck : coverCheck .D4 d4Reps d4Cover = true := by decide +kernel

end CertificateChecks.Batch45

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate45 : (repsCheck .D4 d4Reps = true)
    ∧ (coverCheck .D4 d4Reps d4Cover = true) := by
  exact ⟨CertificateChecks.Batch45.d4_repsCheck, CertificateChecks.Batch45.d4_coverCheck⟩

end Certificates
