module

public import Certificates.Kernel.LocalComp.LaySeeds
public import Certificates.Kernel.LocalComp.LaySnapsLive
public import CFSG.Certificates.Kernel.Common.JsonGz
public import CFSG.Certificates.Kernel.Common.Each
public import CFSG.Certificates.Kernel.Common.ForallChunks
import CFSG.Certificates.Kernel.Common.Repo
import all CFSG.Blueprint.NativeSporadic

set_option maxRecDepth 400000

#lay_seeds CertificateChecks.KernelNC2.Ly.L 5 111
  CFSG.Blueprint.NativeSporadic.LySeed1 CFSG.Blueprint.NativeSporadic.LySeed2

#kc_repo #lay_snaps_live CertificateChecks.KernelNC2.Ly.P 5 111 CertificateChecks.KernelNC2.Ly.L.A
  CertificateChecks.KernelNC2.Ly.L.B "Certificates/Kernel/Census/NC2/data/ly.json.gz" 98478
  5305194283822023324

#kc_repo #kc_json_gz CertificateChecks.KernelNC2.Ly.D
  "Certificates/Kernel/Census/NC2/data/ly.json.gz" 98478 5305194283822023324
  (a : Nat) (tests : List Nat) (oddExp : Nat) (extra : List Nat) (sq : List Nat)
  (cj : List (List Nat)) (sig : List Nat) (sigma : List Nat) (tau : List Nat)
  (pairs : List (Nat × Nat))

public section

namespace CertificateChecks.KernelNC2.Ly

open CFSG.KC.NC2L

@[expose] noncomputable def data : NC2LData :=
  { a := D.a, tests := D.tests, oddExp := D.oddExp, extra := D.extra, sq := D.sq, cj := D.cj,
    sig := D.sig, sigma := D.sigma, tau := D.tau, pairs := D.pairs }

@[expose] noncomputable def chunkOK (i : Nat) : Bool :=
  liveL L.lay (P.CL.getD i ⟨0, [], []⟩) (P.SL.getD i []) (P.SL.getD (i + 1) [])

theorem m_eq : P.m = 33 := rfl

#kc_each CertificateChecks.KernelNC2.Ly.chunkOK 0 33

#kc_forall_chunks chain (fun i => chunkOK i = true) 33 CertificateChecks.KernelNC2.Ly.chunkOK 1

theorem nc2_K : nc2L L.lay (P.SL.getD P.m []) data = true := by decide +kernel


end CertificateChecks.KernelNC2.Ly

end
