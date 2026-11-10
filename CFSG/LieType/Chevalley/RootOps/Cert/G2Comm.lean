module

public import Certificates.Certificate72


public section

namespace CFSG.LieType.Chevalley.RootOps

theorem g2_repsCheck : repsCheck .G2 g2Reps = true := by
  exact Certificates.certificate72.1

theorem g2_coverCheck : coverCheck .G2 g2Reps g2Cover = true := by
  exact Certificates.certificate72.2

end CFSG.LieType.Chevalley.RootOps
