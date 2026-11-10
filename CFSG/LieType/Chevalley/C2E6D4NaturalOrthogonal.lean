module

public import CFSG.LieType.Chevalley.C2E6D4Twist

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin

@[expose] def psiDEquiv
    : groupD ≃* orthElementaryGroup (quadPlus 4 K) :=
  (MonoidHom.ofInjective psiD_injective).trans (MulEquiv.subgroupCongr range_psiD)


end CFSG.LieType.Chevalley.C2E6Std
