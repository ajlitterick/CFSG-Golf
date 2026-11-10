module

public import Certificates.Certificate59


public section

namespace CFSG.LieType.Chevalley.RootOps

theorem e8_repsCheck : repsCheck .E8 e8Reps = true := by
  exact Certificates.certificate59.1

theorem e8_coverCheck : coverCheck .E8 e8Reps e8Cover = true := by
  exact Certificates.certificate59.2

end CFSG.LieType.Chevalley.RootOps
