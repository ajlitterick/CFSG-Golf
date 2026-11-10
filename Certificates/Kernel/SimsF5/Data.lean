module

public import Certificates.Data.Kernel.SimsF5.Defs
public import Certificates.Data.Kernel.CosetLat.Defs
public import Certificates.Data.Kernel.Misc.PermClos
import CFSG.Certificates.Kernel.Common.HarnessGzTree
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 EL
  "Certificates/Kernel/SimsF5/data/el.bin.gz" 27 4 756 5461998891245028499
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 TE
  "Certificates/Kernel/SimsF5/data/te.bin.gz" 27 4 3456 15754539143771265284
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 TP
  "Certificates/Kernel/SimsF5/data/tp.bin.gz" 4 4 512 16515373528767269824
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 TS
  "Certificates/Kernel/SimsF5/data/ts.bin.gz" 4 4 512 14795347859664200904
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 TC
  "Certificates/Kernel/SimsF5/data/tc.bin.gz" 4 4 3584 14601873986252540200
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 UE
  "Certificates/Kernel/SimsF5/data/ue.bin.gz" 27 4 10935 7686754580898558560
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 UR
  "Certificates/Kernel/SimsF5/data/ur.bin.gz" 4 4 1620 13100182974232661115
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 CR
  "Certificates/Kernel/SimsF5/data/cr.bin.gz" 8 4 27840 3411920031142834457
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 MJ
  "Certificates/Kernel/SimsF5/data/mj.bin.gz" 4 4 120 12672152233972531851
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 SE
  "Certificates/Kernel/SimsF5/data/se.bin.gz" 27 4 2808 6842432780095940297
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 SP
  "Certificates/Kernel/SimsF5/data/sp.bin.gz" 4 4 416 1556692485785290591
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 SS
  "Certificates/Kernel/SimsF5/data/ss.bin.gz" 4 4 416 14261729517050746571
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 SC
  "Certificates/Kernel/SimsF5/data/sc.bin.gz" 4 4 1424 15450023617486633423
#kc_repo #kc_ktree_gz CertificateChecks.KernelSimsF5 SK
  "Certificates/Kernel/SimsF5/data/sk.bin.gz" 27 4 270 18402132722208739806
#kc_repo #kc_json_gz CertificateChecks.KernelSimsF5
  "Certificates/Kernel/SimsF5/data/w7600.json.gz" 1959 7731903421891008872
  (subW : List (List Nat)) (repW : List (List (List Nat))) (joinW : List (List (List Nat)))
  (incW : List (List (List Nat)))

public section

namespace CertificateChecks.KernelSimsF5

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.Clos CFSG.KC.CosetLat CFSG.KC.SimsF5


@[expose] noncomputable def LG (t j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (EL (Nat.add (nat_lit 6) t)) (EL j) (Nat.blt j (nat_lit 7))


@[expose] noncomputable def ch7600m0 (s : Nat) : Bool :=
  allR (Nat.mul (nat_lit 81) s) (nat_lit 81)
    (ctabAt m6 (LG (nat_lit 5)) (nat_lit 8) TE (nat_lit 128) UE (nat_lit 405) CR)


end CertificateChecks.KernelSimsF5

end
