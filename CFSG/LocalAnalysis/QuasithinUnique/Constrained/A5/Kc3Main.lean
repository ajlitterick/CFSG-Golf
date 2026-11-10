module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3L4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3F4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3L5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3Sp4
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M22
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M23
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3M24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3G2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3D4
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery

public section

namespace CFSG.QuasithinUnique.A5

structure Kc3Residual : Prop where
  j4 : Kc3For (Kc3Spor .J4)
  hs : Kc3For (Kc3Spor .HS)
  he : Kc3For (Kc3Spor .He)
  ru : Kc3For (Kc3Spor .Ru)

theorem kc3Inspection_of_residual
    (h : Kc3Residual) : Kc3Inspection :=
  kc3Inspection_of_families
    { psl3 := kc3For_psl3
      psp4 := kc3For_psp4
      g2 := kc3For_g2_of_even kc3For_g2_even
      d4 := kc3For_d4_of_even kc3For_d4_even
      f4 := kc3For_f4
      tits := kc3For_tits
      l4 := kc3For_L4
      l5 := kc3For_l5
      m22 := kc3For_of_localFor (isoInv_spor .M22) kc3LocalFor_m22
      m23 := kc3For_of_localFor (isoInv_spor .M23) kc3LocalFor_m23
      m24 := kc3For_of_localFor (isoInv_spor .M24) kc3LocalFor_m24
      j4 := h.j4
      hs := h.hs
      he := h.he
      ru := h.ru }

end CFSG.QuasithinUnique.A5
