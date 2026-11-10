module

import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.Sporadic.Fi24Fix.Data

public section

namespace CFSG.KD.Fi24Fix.Neg

open CFSG.KC.Ord CFSG.KC.Fi24Fix CFSG.KD.BrFi24 CFSG.KD.Fi24Fix

theorem keeps8 : notB (keepsOK MUL Q (RB 9)) = true := by quickRfl


end CFSG.KD.Fi24Fix.Neg

end
