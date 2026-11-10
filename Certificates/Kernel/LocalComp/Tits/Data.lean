module

public import Certificates.Kernel.Sporadic.RawGen
import Certificates.Kernel.Misc.Perm.HexCmd
meta import Certificates.Data.CFSGNative.SectionRank.TitsChain
public import CFSG.Certificates.Kernel.Bounds.Core3
import CFSG.Certificates.Kernel.Bounds.Load

set_option maxRecDepth 400000

namespace CertificateChecks.KernelLC.Tits

open CFSG.SectionRank.Native.Tits


meta def genM : Array (Array Nat) := (genTables ()).map fun t => t.map (·.toNat)


end CertificateChecks.KernelLC.Tits

#kc_items CertificateChecks.KernelLC.Tits.TP include_bytes "data/Data.TP.items" 19054 13889954586301689919
#kc_items CertificateChecks.KernelLC.Tits.TG include_bytes "data/Data.TG.items" 9672 17672028335351280158
#kc_items CertificateChecks.KernelLC.Tits.TR include_bytes "data/Data.TR.items" 15280 15779094633519677415
