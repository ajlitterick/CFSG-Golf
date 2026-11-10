module

public import Certificates.Certificate67


public section

namespace CFSG.LieType.Chevalley.RootOps

theorem e8_tabCheck : tabCheck .E8 = true := by
  exact Certificates.certificate67.1

theorem e8_allValid : allValid .E8 = true := by
  exact Certificates.certificate67.2

end CFSG.LieType.Chevalley.RootOps
