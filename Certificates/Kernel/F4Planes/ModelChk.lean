module

public import Certificates.Data.Kernel.F4Planes
public import Certificates.Kernel.F4Syl3.ModelChk
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Repo

public section

#kc_repo #kc_json_gz CFSG.KD.F4Planes "Certificates/Kernel/F4Planes/data/model.json.gz" 26952
  4247695855319381425 (VT : Nat) (AT : Nat) (QT : Nat) (OM : Nat) (PR : Nat) (rows : List (List (Nat × Nat × Nat)))

#kc_each CFSG.KD.F4Planes.ch14950pl r (fun k => CFSG.KC.F4Planes.rowK CFSG.KD.F4Planes.VT
  CFSG.KD.F4Planes.AT CFSG.KD.F4Planes.QT CFSG.KD.F4Planes.OM CFSG.KD.F4Planes.PR
  CFSG.KD.F4Syl3.reps CFSG.KD.F4Planes.rows k) 0 48

namespace CFSG.KD.F4Planes

open CFSG.KC.F4Planes

theorem tab_ok : tabChk VT AT QT = true := by quickRfl

theorem om_ok : omChk VT AT QT OM = true := by quickRfl

theorem rep_ok : repChk VT AT QT PR = true := by quickRfl


end CFSG.KD.F4Planes

end
