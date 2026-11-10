module

public import CFSG.LieType.Steinberg.Adjoint.CertE6ValidInputs

public section

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

namespace CertificateChecks.Batch122

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley

private theorem e6AdjData_nR : AdjData.nR .E6 = 72 := by decide +kernel

end CertificateChecks.Batch122

namespace Certificates

open CertificateChecks

open CFSG CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint in
open CFSG.Blueprint.Chevalley in
theorem certificate122 : (AdjData.nR .E6 = 72) := by
  exact CertificateChecks.Batch122.e6AdjData_nR

end Certificates
