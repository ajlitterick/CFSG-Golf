module

public import CFSG.ClassicalInvolution.Uniform.UFacade
public import CFSG.ClassicalInvolution.Uniform.UOmega4
public import CFSG.ClassicalInvolution.Uniform.USaturate
public import CFSG.ClassicalInvolution.Uniform.USylow

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77
open scoped MatrixGroups

section Omega4Three

variable {G : Type} [Group G] [Finite G] {K₀ : Subgroup G} {z₀ : G}


end Omega4Three

section ThmI

variable {t : MemberType} {F : Type} [Group F] [Finite F] {K : Subgroup F} {z : F}


end ThmI

section FusionCore

@[expose] def TwoElementsNormalizeU (t : MemberType) : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ∀ (K : Subgroup F) (z : F), IsClassicalMemberU t K z → IsIntrinsicU t K z →
      Hat2A7R.TwoElementsNormalize K z


end FusionCore

end CFSG.ClassicalInvolution.Uniform
