module

public import CFSG.ClassicalInvolution.RouteD.TWT8Case

public section

namespace CFSG.ClassicalInvolution.RouteD.TWT8

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Asc77
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin

local notation "𝒞" => CoreAssembly.conjClass

set_option linter.unusedSectionVars false

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem twinTDExistsCase_five (hΩall : HypOmegaModAll p f) (hP4 : Ih8G2D4 p f)
    (hH : TwinFrameHyp51 p f) (hcls : TwinInvolution p f) : TwinTDExistsCase p f 5 :=
  twinTDExistsCase_of_case (by norm_num) (twinTDCase_five hΩall hP4 hH hcls)

end Main

end CFSG.ClassicalInvolution.RouteD.TWT8
