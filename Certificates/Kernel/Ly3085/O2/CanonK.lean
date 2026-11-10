module

public import Certificates.Kernel.Ly3085.O2.Data
public import Certificates.Data.Kernel.LyOmega.Canon
import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.Repo

namespace CFSG.KD.LyO2

#kc_repo #kc_each_rows CFSG.KD.LyO2 cn (fun _ b₀ c => CFSG.KC.LyOm.canonRange KX b₀ c)
  "Certificates/Kernel/Ly3085/O2/data/canon.txt.gz" 356 8603939073109531078 0 30

end CFSG.KD.LyO2

public section

namespace CFSG.KD.LyO2

theorem cover : Nat.ble n (Nat.mul 64 15137) = true := by quickRfl


end CFSG.KD.LyO2

end
