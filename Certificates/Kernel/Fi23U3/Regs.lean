module

public import Certificates.Kernel.Fi23U3.Snaps
public import Certificates.Kernel.LocalComp.LaySnapsFrom
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

set_option maxRecDepth 400000
set_option Elab.async false

#kc_repo #kc_json_gz CertificateChecks.KernelFi23U3.D "Certificates/Kernel/Fi23U3/data/chain.json.gz"
  10930 3410109472472256960 (cs : List CFSG.KC.OpsLayK.RChunk) (B : List (List Nat))
  (G : List (List Nat)) (T : List (List Nat))

#lay_snaps_from CertificateChecks.KernelFi23U3.Q 3 253 CertificateChecks.KernelFi23U3.S.S5
  CertificateChecks.KernelFi23U3.D.cs

public section

namespace CertificateChecks.KernelFi23U3

open CFSG.KC.OpsLayK CertificateChecks.KernelTc.Fi23


theorem q0_eq : Q.S0 = S.S5 := rfl

@[expose] noncomputable def rc (i : Nat) : Bool :=
  chunkV lay (D.cs.getD i (0, [], [])) (Q.SL.getD i []) (Q.SL.getD (i + 1) [])

#kc_each rc 0 4

#kc_forall_tree rc_all (fun i => rc i = true) 4 CertificateChecks.KernelFi23U3.rc


@[expose] noncomputable def M₀ : List Nat := (Q.SL.getD 4 []).reverse

end CertificateChecks.KernelFi23U3

end
