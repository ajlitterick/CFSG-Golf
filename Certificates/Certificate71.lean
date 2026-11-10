module

public import CFSG.LieType.Chevalley.RootOps.Instance

public section

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

namespace CertificateChecks.Batch71

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps

private theorem f4_tabCheck : tabCheck .F4 = true := by decide +kernel

private theorem f4_allValid : allValid .F4 = true := by decide +kernel

end CertificateChecks.Batch71

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps in
theorem certificate71 : (tabCheck .F4 = true)
    ∧ (allValid .F4 = true) := by
  exact ⟨CertificateChecks.Batch71.f4_tabCheck, CertificateChecks.Batch71.f4_allValid⟩

end Certificates
