module

public import CFSG.Monster.Existence.TwoPoint.Fi23Check
public import CFSG.Monster.Existence.TwoPoint.ThreeVData

public section

namespace CFSG.Monster.Existence

open CFSG.Monster.AxisCount

@[expose] def fiWAlphaGamma : List Native.Gen := fiWU[0]! ++ fiWAlpha


theorem fiConj3VCheck_spec
    (h : wordLin (fiRhoT ++ fiCAlphaGamma) = wordLin (fiCAlphaGamma ++ fiWAlphaGamma)) :
    wordLin fiCAlphaGamma * wordLin fiRhoT = wordLin fiWAlphaGamma * wordLin fiCAlphaGamma := by
  rwa [wordLin_append, wordLin_append] at h

end CFSG.Monster.Existence
