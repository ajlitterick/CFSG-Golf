module

public import CFSG.GH74.GLS.Stage4.Q9.TablesInputs
public import Certificates.Data.Kernel.Q9SL.Defs

public section

namespace CFSG.KC.Q9SL

open CFSG.GH74.GLS.Stage4.Q9

@[expose] def eF (a : F9) : Nat := Nat.add (Nat.mul 3 a.re.val) a.im.val


end CFSG.KC.Q9SL
