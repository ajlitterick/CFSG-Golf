module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionTop
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LieCross

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.AGLEmbeddingD2

@[expose] def GGKFLieSeitz (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ p ≠ d.1.characteristic ∧
    ¬ IsD2SeitzException p d.1

@[expose] def GGKFLieSeitzException (i : TauCeti.CFSGIndex) (p : ℕ) : Prop :=
  ∃ d : TauCeti.ValidLieTypeIndex, i = .lie d ∧ IsD2SeitzException p d.1


end CFSG.StandardType
