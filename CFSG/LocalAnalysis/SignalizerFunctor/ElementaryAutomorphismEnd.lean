module

public import CFSG.LocalAnalysis.SignalizerFunctor.QuadraticEndomorphisms

public section

universe groupUniverse

namespace CFSG.SignalizerFunctor.Helpers

variable {GroupType : Type groupUniverse} [CommGroup GroupType]

@[expose] def elementaryAutomorphismEnd (prime : ℕ) [Module (ZMod prime) (Additive GroupType)] :
    MulAut GroupType →* Module.End (ZMod prime) (Additive GroupType) where
  toFun automorphism := AddMonoidHom.toZModLinearMap prime automorphism.toAdditive.toAddMonoidHom
  map_one' := by ext element; rfl
  map_mul' first second := by ext element; rfl

theorem elementary_automorphism_end_apply (prime : ℕ)
    [Module (ZMod prime) (Additive GroupType)] (automorphism : MulAut GroupType)
    (element : Additive GroupType) :
    elementaryAutomorphismEnd prime automorphism element = Additive.ofMul (automorphism element.toMul) := rfl

theorem elementary_automorphism_end_injective (prime : ℕ)
    [Module (ZMod prime) (Additive GroupType)] :
    Function.Injective (elementaryAutomorphismEnd (GroupType := GroupType) prime) := by
  intro first second equal
  apply MulEquiv.ext
  intro element
  exact congrArg (fun operator => (operator (Additive.ofMul element)).toMul) equal


end CFSG.SignalizerFunctor.Helpers
