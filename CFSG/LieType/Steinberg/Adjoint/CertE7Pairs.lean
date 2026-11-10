module

public import Certificates.Certificate78


public section

namespace CFSG.LieType.Steinberg.Adjoint

theorem e7AdjData_checkPairs_0 : e7AdjData.checkPairsRange 0 18 = true := by
  exact Certificates.certificate78.1

theorem e7AdjData_checkPairs_1 : e7AdjData.checkPairsRange 18 18 = true := by
  exact Certificates.certificate78.2.1

theorem e7AdjData_checkPairs_2 : e7AdjData.checkPairsRange 36 18 = true := by
  exact Certificates.certificate78.2.2.1

theorem e7AdjData_checkPairs_3 : e7AdjData.checkPairsRange 54 18 = true := by
  exact Certificates.certificate78.2.2.2.1

theorem e7AdjData_checkPairs_4 : e7AdjData.checkPairsRange 72 18 = true := by
  exact Certificates.certificate78.2.2.2.2.1

theorem e7AdjData_checkPairs_5 : e7AdjData.checkPairsRange 90 18 = true := by
  exact Certificates.certificate78.2.2.2.2.2.1

theorem e7AdjData_checkPairs_6 : e7AdjData.checkPairsRange 108 18 = true := by
  exact Certificates.certificate78.2.2.2.2.2.2

end CFSG.LieType.Steinberg.Adjoint
