module

public import Certificates.Certificate53


public section

namespace CFSG.LieType.Chevalley.RootOps

theorem e7_repsCheck : repsCheck .E7 e7Reps = true := by
  exact Certificates.certificate53.1

theorem e7_coverCheck : coverCheck .E7 e7Reps e7Cover = true := by
  exact Certificates.certificate53.2

end CFSG.LieType.Chevalley.RootOps
