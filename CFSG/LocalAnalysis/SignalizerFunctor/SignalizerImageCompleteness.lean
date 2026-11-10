module

public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerImageLifting

public section

open CFSG.Open

universe groupUniverse imageUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [Group GroupType] [Finite GroupType]
variable {ImageType : Type imageUniverse} [Group ImageType]


end CFSG.SignalizerFunctor.Helpers
