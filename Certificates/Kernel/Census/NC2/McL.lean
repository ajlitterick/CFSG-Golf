module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Kernel.LocalComp.LaySnapsLive
public import CFSG.Certificates.Kernel.Common.JsonGz
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Repo
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelNC2.McL.L 3 21
  CFSG.Blueprint.NativeSporadic.McLSeed1 CFSG.Blueprint.NativeSporadic.McLSeed2

#kc_repo #lay_snaps_live CertificateChecks.KernelNC2.McL.P 3 21 CertificateChecks.KernelNC2.McL.L.A
  CertificateChecks.KernelNC2.McL.L.B "Certificates/Kernel/Census/NC2/data/mcl.json.gz" 31675
  15221677160061111283

#kc_repo #kc_json_gz CertificateChecks.KernelNC2.McL.D
  "Certificates/Kernel/Census/NC2/data/mcl.json.gz" 31675 15221677160061111283
  (a : Nat) (tests : List Nat) (oddExp : Nat) (extra : List Nat) (sq : List Nat)
  (cj : List (List Nat)) (sig : List Nat) (sigma : List Nat) (tau : List Nat)
  (pairs : List (Nat × Nat))

public section

namespace CertificateChecks.KernelNC2.McL

open CFSG.KC.NC2L

@[expose] noncomputable def data : NC2LData :=
  { a := D.a, tests := D.tests, oddExp := D.oddExp, extra := D.extra, sq := D.sq, cj := D.cj,
    sig := D.sig, sigma := D.sigma, tau := D.tau, pairs := D.pairs }

@[expose] noncomputable def chunkOK (i : Nat) : Bool :=
  liveL L.lay (P.CL.getD i ⟨0, [], []⟩) (P.SL.getD i []) (P.SL.getD (i + 1) [])

theorem m_eq : P.m = 11 := rfl

#kc_each CertificateChecks.KernelNC2.McL.chunkOK 0 11

#kc_forall_chunks chain (fun i => chunkOK i = true) 11 CertificateChecks.KernelNC2.McL.chunkOK 1

theorem nc2_K : nc2L L.lay (P.SL.getD P.m []) data = true := by decide +kernel


end CertificateChecks.KernelNC2.McL

end
