module

public import CFSG.Monster.Existence.TwoPoint.Fi23Check
public import CFSG.Monster.Existence.TwoPoint.Fi23S4Data

public section

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.Monster.B.Short


@[expose] def s4WBetaGamma : List Native.Gen := s4WGamma ++ fiWBeta


@[expose] def s4WE8Gamma : List Native.Gen := s4WGamma ++ fiWU[8]!


@[expose] def s4WAlphaGamma : List Native.Gen := s4WGamma ++ fiWAlpha


theorem s4ConjCheck_parts
    (h : wordLin (fiRhoT ++ s4CGamma) = wordLin (s4CGamma ++ s4WGamma) ∧
      wordLin (fiRhoT ++ s4CBetaGamma) = wordLin (s4CBetaGamma ++ s4WBetaGamma)) :
    wordLin s4CGamma * wordLin fiRhoT = wordLin s4WGamma * wordLin s4CGamma ∧
      wordLin s4CBetaGamma * wordLin fiRhoT = wordLin s4WBetaGamma * wordLin s4CBetaGamma := by
  obtain ⟨h1, h2⟩ := h
  rw [wordLin_append, wordLin_append] at h1 h2
  exact ⟨h1, h2⟩

end CFSG.Monster.Existence
