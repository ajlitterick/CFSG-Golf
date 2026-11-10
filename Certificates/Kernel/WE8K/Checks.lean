module

public import Certificates.Kernel.WE8K.Orbits
public import Certificates.Kernel.WE8K.SymA
public import Certificates.Kernel.WE8K.SymB
import CFSG.Certificates.Kernel.Common.ForallTree

set_option maxRecDepth 400000

public section

namespace CFSG.KD.WE8K

open CFSG.KC.WE8K CFSG.KC.Loop

#kc_forall_tree ch18004_orbAll (fun k => orbFam k = true) 5 CFSG.KD.WE8K.ch18004o

theorem ch18004_orb8 : orbFam 8 = true := ch18004o8

theorem ch18004_orb9 : orbFam 9 = true := ch18004o9

#kc_forall_tree ch18004_symPAll (fun k => symPFam k = true) 21 CFSG.KD.WE8K.ch18004p

#kc_forall_tree ch18004_symMAll (fun k => symMFam k = true) 2 CFSG.KD.WE8K.ch18004m

theorem ch18004_oN : oN = [120, 3780, 37800, 113400, 3150, 37800, 3780, 120, 1, 15120] := rfl


end CFSG.KD.WE8K

end
