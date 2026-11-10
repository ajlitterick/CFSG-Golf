module

public import CFSG.Certificates.Kernel.Bounds.LyAlt.Data.Sel
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CFSG.KD.LyA

open CFSG.KC.LyA.DceS


theorem xWords : wordsOK WD CFSG.KC.LyA.rel LI NL NR WH nW = true := by quickRfl


end CFSG.KD.LyA

end
