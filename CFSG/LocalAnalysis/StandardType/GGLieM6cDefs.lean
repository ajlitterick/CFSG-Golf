module

public import CFSG.LocalAnalysis.StandardType.GGFinModelRat

public section

namespace CFSG.StandardType.LieCore.M6c

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType.GGFinModel
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule

@[expose] def GGLieAbelianPreimageE6
    (A : Subgroup (ModGL Tag.E6 GGL)) : Prop :=
  ∀ (k : Type) [Field k] [Finite k] (ι : k →+* GGL) (x y : ↥(e6Data_valid.minGroup k)),
    baseChangeGL ι (e6Isogeny k x : ModGL Tag.E6 k) ∈ A →
    baseChangeGL ι (e6Isogeny k y : ModGL Tag.E6 k) ∈ A → x * y = y * x

end CFSG.StandardType.LieCore.M6c
