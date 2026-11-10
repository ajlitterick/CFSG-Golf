module

public import Certificates.Data.Kernel.J4DCE.TrioSteps
import CFSG.Certificates.Kernel.M24G.ImgSound

public section

namespace CFSG.KC.J4DCE

open CFSG.Quasithin.H13.AS91.M24G

local notation "T3" => Nat × Nat × Nat

private abbrev jS : Type := Array T3 × Std.HashMap Nat Nat × Nat


private abbrev kS : Type := Array T3 × Array Nat × Array Nat × Std.HashMap Nat Nat × Nat


private def proj (st : kS) : jS := (st.1, st.2.2.2.1, st.2.2.2.2)


end CFSG.KC.J4DCE
