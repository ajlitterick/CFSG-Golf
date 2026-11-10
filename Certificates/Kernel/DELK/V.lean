module

public import Certificates.Kernel.DELK.D
public import Certificates.Data.Kernel.DELKWF

public section

namespace CFSG.KD.DELK

open Certificates.DELK

theorem pairsOK : kPairsOK P = true := by decide +kernel

theorem conjShapes : kConjShapes C = true := by decide +kernel


end CFSG.KD.DELK

end
