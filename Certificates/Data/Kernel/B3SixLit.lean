module

import CFSG.Certificates.Kernel.Common.Eval
meta import Certificates.Data.Kernel.B3SixEval
public import CFSG.Quasithin.Background.B3FourData
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Background.B1
public import CFSG.Quasithin.Background.B3Q
public import CFSG.Quasithin.Background.B3VMod

#kc_eval CFSG.KC.B3Six dG0 CFSG.KC.B3Six.Ev.four 0 1
#kc_eval CFSG.KC.B3Six dGT0 CFSG.KC.B3Six.Ev.four 1 1
#kc_eval CFSG.KC.B3Six dL0 CFSG.KC.B3Six.Ev.four 0 0
#kc_eval CFSG.KC.B3Six dLT0 CFSG.KC.B3Six.Ev.four 1 0

public section

namespace CFSG.KC.B3Six

open CFSG.Quasithin.B3


end CFSG.KC.B3Six

end
