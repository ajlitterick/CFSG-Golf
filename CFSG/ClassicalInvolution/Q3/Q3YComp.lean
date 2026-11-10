module

public import CFSG.ClassicalInvolution.Q3.Generation
public import CFSG.ClassicalInvolution.Q3.Q3YAbs

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank


namespace Q3Y

section Excluded


end Excluded

section Pair

theorem eq_top_of_mem_fund_sl23 {c : CompData} (hc : c = CompData.sl23) {R : Subgroup c.G}
    (hR : R ∈ c.fund) : R = ⊤ := by
  subst hc
  exact Set.mem_singleton_iff.mp hR


end Pair

end Q3Y

section Main


end Main

end CFSG.ClassicalInvolution.Q3
