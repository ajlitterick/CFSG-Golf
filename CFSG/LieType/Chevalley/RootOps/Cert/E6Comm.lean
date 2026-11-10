module

public import Certificates.Certificate49


public section

namespace CFSG.LieType.Chevalley.RootOps

theorem e6_repsCheck : repsCheck .E6 e6Reps = true := by
  exact Certificates.certificate49.1

theorem e6_coverCheck : coverCheck .E6 e6Reps e6Cover = true := by
  exact Certificates.certificate49.2

end CFSG.LieType.Chevalley.RootOps
