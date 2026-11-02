module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFamilies
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL3
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListHat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL2sq
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListG2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListD4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL4L5
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListTits
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListF4
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBender
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSU3
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM12
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM11
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.Sporadic.Schreier.TitsOther

public section

namespace CFSG.QuasithinUnique.Vol2Native.A312L

structure A312Residual : Prop where
  l3odd : FamL3odd
  u3odd : FamU3odd
  m22 : FamM22
  m23 : FamM23
  m24 : FamM24
  j1 : FamJ1
  j2 : FamJ2
  j4 : FamJ4
  hs : FamHs
  he : FamHe
  ru : FamRu
  sl3odd : FamSl3odd
  hat7 : FamHat7
  hatM22 : FamHatM22

theorem a312Families_of_residual
    (hR : A312Residual) : A312Families where
  alt6 := alt6
  alt7 := alt7
  l2p := l2p
  l2psq := l2psq
  l3odd := hR.l3odd
  u3odd := hR.u3odd
  l2even := l2even
  l3even := l3even
  u3even := u3even
  sp4 := sp4
  g2 := g2
  d4 := d4
  f4 := f4
  sz := sz
  tits := tits
  l4 := l4
  l5 := l5
  m11 := m11
  m12 := m12
  m22 := hR.m22
  m23 := hR.m23
  m24 := hR.m24
  j1 := hR.j1
  j2 := hR.j2
  j4 := hR.j4
  hs := hR.hs
  he := hR.he
  ru := hR.ru
  sl3even := famSl3even_of_minus sl3evenMinus
  sl3odd := hR.sl3odd
  hat6 := hat6
  hat7 := hR.hat7
  hatM22 := hR.hatM22

theorem a312ListFactsCat_of_residual
    (hT : ThreeCoverFactCat) (hR : A312Residual) :
    A312ListFactsCat :=
  a312ListFactsCat_of_families hT (a312Families_of_residual hR)

end CFSG.QuasithinUnique.Vol2Native.A312L
