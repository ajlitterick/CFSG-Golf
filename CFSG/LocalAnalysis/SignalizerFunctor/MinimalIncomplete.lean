module

public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeTransitivity
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerImageCompleteness
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerSpectrum
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerConditions

public section

open CFSG.Open

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]


end CFSG.SignalizerFunctor.Helpers
