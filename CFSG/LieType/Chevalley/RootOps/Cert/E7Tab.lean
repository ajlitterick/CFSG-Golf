module

public import Certificates.Certificate58


public section

namespace CFSG.LieType.Chevalley.RootOps

theorem e7_tabCheck : tabCheck .E7 = true := by
  exact Certificates.certificate58.1

theorem e7_allValid : allValid .E7 = true := by
  exact Certificates.certificate58.2

end CFSG.LieType.Chevalley.RootOps
