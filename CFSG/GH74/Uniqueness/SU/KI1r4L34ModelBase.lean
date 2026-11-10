
module

public meta import CFSG.GH74.KGroups.L34AutBase
public meta import CFSG.GH74.KGroups.L34Base
public meta import CFSG.GH74.KGroups.Checks
public import CFSG.GH74.Uniqueness.SU.KI1r4L34ModelInputs
public meta import CFSG.GH74.Uniqueness.SU.KI1r4L34ModelInputs

@[expose] public section

namespace CFSG.GH74.Uniqueness.SU.K.R4.L34M

open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.GH74.KGroups CFSG.GH74.KGroups.L34

theorem QA_closure' : QA.originalSubgroup =
    Subgroup.closure {g | g ∈ [PA, PB, sg0, sg1, sg2]} := by
  rw [QA, certificate_originalSubgroup]

end CFSG.GH74.Uniqueness.SU.K.R4.L34M
