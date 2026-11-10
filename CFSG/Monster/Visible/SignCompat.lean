module

public import CFSG.Monster.Visible.SignCompat.Triality
public import CFSG.Monster.Visible.Kernel
public import CFSG.Monster.Generated.Data

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess CFSG.Monster.Generated Matrix

theorem rhoEquiv_XQ_conj_mem_Hmat (e : Parker) : tauB * rhoEquiv (XQ e) * tauB⁻¹ ∈ Hmat :=
  (thetaEquiv_signLiftPair e) ▸ thetaEquiv_mem_Gvis (signLiftPair e)


end CFSG.Monster.Visible
