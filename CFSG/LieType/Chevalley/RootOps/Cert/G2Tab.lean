module

public import Certificates.Certificate75


public section

namespace CFSG.LieType.Chevalley.RootOps

theorem g2_tabCheck : tabCheck .G2 = true := by
  exact Certificates.certificate75.1

theorem g2_allValid : allValid .G2 = true := by
  exact Certificates.certificate75.2

end CFSG.LieType.Chevalley.RootOps
