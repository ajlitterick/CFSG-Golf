module

public import Certificates.Certificate119


public section

namespace CFSG.LieType.Steinberg.Adjoint

open CFSG.Blueprint.Chevalley

theorem e7AdjData_checkTables : e7AdjData.checkTables = true := by
  exact Certificates.certificate119.1

theorem e7AdjData_checkSimple : e7AdjData.checkSimple = true := by
  exact Certificates.certificate119.2.1

theorem e7AdjData_checkPairNorm : e7AdjData.checkPairNorm = true := by
  exact Certificates.certificate119.2.2.1

theorem e7AdjData_nR : AdjData.nR .E7 = 126 := by
  exact Certificates.certificate119.2.2.2.1

theorem e7AdjData_checkWeyl : e7AdjData.checkWeyl = true := by
  rw [AdjData.checkWeyl, e7AdjData_nR, show (126 : ℕ) = 7 * 18 from rfl]
  refine e7AdjData.checkWeylRange_of_slices 0 18 7 fun s hs => ?_
  interval_cases s
  exacts [e7AdjData_checkWeyl_0, e7AdjData_checkWeyl_1, e7AdjData_checkWeyl_2,
    e7AdjData_checkWeyl_3, e7AdjData_checkWeyl_4, e7AdjData_checkWeyl_5, e7AdjData_checkWeyl_6]

theorem e7AdjData_checkPairs : e7AdjData.checkPairs = true := by
  rw [AdjData.checkPairs, e7AdjData_nR, show (126 : ℕ) = 7 * 18 from rfl]
  refine e7AdjData.checkPairsRange_of_slices 0 18 7 fun s hs => ?_
  interval_cases s
  exacts [e7AdjData_checkPairs_0, e7AdjData_checkPairs_1, e7AdjData_checkPairs_2,
    e7AdjData_checkPairs_3, e7AdjData_checkPairs_4, e7AdjData_checkPairs_5,
    e7AdjData_checkPairs_6]

theorem e7AdjData_valid : e7AdjData.Valid :=
  ⟨e7AdjData_checkTables, e7AdjData_checkSimple, e7AdjData_checkWeyl, e7AdjData_checkPairs,
    e7AdjData_checkPairNorm⟩


end CFSG.LieType.Steinberg.Adjoint
