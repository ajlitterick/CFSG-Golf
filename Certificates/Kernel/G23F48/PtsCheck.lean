module

public import Certificates.Kernel.G23F48.A22Check
public import Certificates.Kernel.G23F48.FrameCheck
public import Certificates.Kernel.Misc.Perm.CharsCat
public import Certificates.Data.Kernel.G23F48.Pts
public meta import CFSG.Milestones.ASVolI.F48.Rest.G23Inputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

#ks_chars_cat CFSG.KC.G23F48.PtsT CFSG.ASVolI.burnsideF48t_g23PtsStr
#kmisc_hexflat CFSG.KC.G23F48.PtsT CFSG.ASVolI.burnsideF48t_g23PtsStr 1 14 2 728

namespace CFSG.KC.G23F48

open CFSG.ASVolI

meta def matsM : Array (Array Nat) := burnsideF48t_g23Mats ()

end CFSG.KC.G23F48

#kmisc_packarrs CFSG.KC.G23F48.MP CFSG.KC.G23F48.matsM 2

namespace CFSG.KC.G23F48

open CFSG.ASVolI CFSG.KC.Enum CFSG.KS CFSG.KC.Misc.ArrEnum


end CFSG.KC.G23F48

end
