module

public import CFSG.ClassicalInvolution.SubnormalClosure.Reduction
public import CFSG.ClassicalInvolution.Reduction
import CFSG.Adapters.GeneralizedFitting
import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open

theorem genFittingFStar_normal (G : Type*) [Group G] : (genFittingFStar G).Normal :=
  CFSG.ComponentClassification.GeneralizedFitting.normal G


end CFSG.ClassicalInvolution
