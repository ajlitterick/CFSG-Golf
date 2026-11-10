module

public import Certificates.Data.Kernel.L5.Sh2E16
import CFSG.Certificates.Kernel.Common.Each

public section

namespace CFSG.KD.L5.E16

open CFSG.Certificates.Kernel.L5S

set_option maxRecDepth 100000

theorem tabsE16_true : tabsE16 = true := by decide +kernel

#kc_each CFSG.KD.L5.E16.ch5068 0 4


end CFSG.KD.L5.E16

end
