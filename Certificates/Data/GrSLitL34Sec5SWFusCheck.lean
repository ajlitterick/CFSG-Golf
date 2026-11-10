module

public import Certificates.Data.GrSLitL34Sec5SWIsoCheck

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

open CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def commKB (kb : List Bool) (x y : MElt) : Bool := eqKB kb (mulM x y) (mulM y x)


@[expose] def zInvs : List MElt := [(0, 2, 0), (0, 0, 2), (0, 2, 2)]


end CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso
