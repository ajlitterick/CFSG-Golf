module

public import Certificates.Certificate45


public section

namespace CFSG.LieType.Chevalley.RootOps

theorem d4_repsCheck : repsCheck .D4 d4Reps = true := by
  exact Certificates.certificate45.1

theorem d4_coverCheck : coverCheck .D4 d4Reps d4Cover = true := by
  exact Certificates.certificate45.2

end CFSG.LieType.Chevalley.RootOps
