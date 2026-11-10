
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatM24Base

public import Certificates.Certificate4068

public section

namespace CFSG.QuasithinUnique.Ch1.SporLat.M24

open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Sporadic.Mathieu (m24a m24b card_M24 m24_hyp)
open CFSG.Open (pCoreOf)

instance m24Lat_of_cert :
    M24Lat :=
  ⟨Certificates.certificate4068.1⟩

section Cert

theorem m24_Y_le_iff {j jj : ℕ} (hj : j < 13) (hjj : jj < 13) :
    m24Ctx.Y j ≤ m24Ctx.Y jj ↔ jj ∈ CFSG.Quasithin.S151S9T.m24Incl[j]! :=
  Certificates.certificate4068.2.1 j hj jj hjj

theorem m24_Y4_le_centralizer {z₀ : ↥CFSG.Blueprint.NativeSporadic.M24}
    (hz : (tab 24 z₀).toArray = m24SLP[162]!) :
    m24Ctx.Y 4 ≤ Subgroup.centralizer ({z₀} : Set ↥CFSG.Blueprint.NativeSporadic.M24) :=
  Certificates.certificate4068.2.2.2.1 z₀ hz

end Cert

end CFSG.QuasithinUnique.Ch1.SporLat.M24
