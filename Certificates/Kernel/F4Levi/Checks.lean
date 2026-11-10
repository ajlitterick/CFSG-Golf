module

public import Certificates.Kernel.F4Levi.Data
public import Certificates.Data.Kernel.F4Levi
import CFSG.Certificates.Kernel.Common.EachTrue

public section

#kc_each CFSG.KD.F4Levi.ch799603el r (fun i => CFSG.KC.F4Levi.elN CFSG.KD.F4Levi.gs
  CFSG.KD.F4Levi.es CFSG.KD.F4Levi.ew CFSG.KD.F4Levi.nx 81 i == 1) 0 81

#kc_each CFSG.KD.F4Levi.ch799603cv r (fun i => CFSG.KC.F4Levi.cvN CFSG.KD.F4Levi.es
  CFSG.KD.F4Levi.cw CFSG.KD.F4Levi.cl CFSG.KD.F4Levi.ri CFSG.KD.F4Levi.ra i == 1) 0 81

namespace CFSG.KD.F4Levi

open CFSG.KC.F4Levi CFSG.KC.F4Syl3

theorem gen_ok : allN 6 (fun l => genN l == 1) = true := by decide +kernel

theorem d3_ok : allN 4 (d3Row dw dl gs) = true := by decide +kernel

theorem inc_ok : incB es = true := by decide +kernel

theorem es_lt : es.all (fun e => Nat.blt e (2 ^ 2704)) = true := by decide +kernel

theorem es_length : es.length = 81 := by decide +kernel


end CFSG.KD.F4Levi

end
