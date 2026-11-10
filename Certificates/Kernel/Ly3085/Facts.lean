
module


public import Certificates.Kernel.Ly3085.Simple

public section

namespace CertificateChecks.KernelLy

open CFSG.Sporadic.Ly

theorem card_J_S [LySeed] :
    Nat.card J = 51765179004000000 := by
  rw [J_eq_JS]
  exact card_JS

theorem isSimpleGroup_J_S [LySeed] :
    IsSimpleGroup J := by
  rw [J_eq_JS]
  exact isSimpleGroup_JS'


end CertificateChecks.KernelLy

end
