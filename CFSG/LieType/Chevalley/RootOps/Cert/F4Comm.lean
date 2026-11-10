module

public import Certificates.Certificate68


public section

namespace CFSG.LieType.Chevalley.RootOps

theorem f4_repsCheck : repsCheck .F4 f4Reps = true := by
  exact Certificates.certificate68.1

theorem f4_coverCheck : coverCheck .F4 f4Reps f4Cover = true := by
  exact Certificates.certificate68.2

end CFSG.LieType.Chevalley.RootOps
