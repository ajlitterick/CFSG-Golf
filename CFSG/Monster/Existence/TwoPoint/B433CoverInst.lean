module

public import CFSG.YGroups.DCE.B433Check
public import CFSG.Monster.Existence.TwoPoint.B433Cover
public import CFSG.Monster.Existence.TwoPoint.B433CoverNodes
public import CFSG.Monster.Existence.TwoPoint.B433CoverLinkInputs

public section

namespace CFSG.Monster.Existence.B433Cover

open CFSG.YGroups CFSG.YGroups.DCE CFSG.YGroups.DCE.B433 CFSG.YGroups.DCE.B433Native
  CFSG.Monster.B.Co2
open CFSG.Certificates.CosetEnumeration (evalWord)


@[expose] noncomputable def xB : ℕ → B433 := nodeProd (fun l => psi (yGen 4 3 2 l)) tB


end CFSG.Monster.Existence.B433Cover
