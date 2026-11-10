module

public import CFSG.Certificates.Kernel.Enum.Defs
public import CFSG.Certificates.Kernel.Local.HN.X.Lib

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KC.LL CFSG.KC.LL.HNX


theorem andB_left {a b : Bool} (h : CFSG.KC.Ord.andB a b = true) : a = true := by
  revert h
  cases a <;> cases b <;> decide


end CFSG.KS.SporSch

end
