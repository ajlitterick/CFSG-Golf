module

public import Certificates.Certificate76


public section

namespace CFSG.LieType.Steinberg.Adjoint

theorem e6AdjData_checkPairs_0 : e6AdjData.checkPairsRange 0 24 = true := by
  exact Certificates.certificate76.1

theorem e6AdjData_checkPairs_1 : e6AdjData.checkPairsRange 24 24 = true := by
  exact Certificates.certificate76.2.1

theorem e6AdjData_checkPairs_2 : e6AdjData.checkPairsRange 48 24 = true := by
  exact Certificates.certificate76.2.2

end CFSG.LieType.Steinberg.Adjoint
