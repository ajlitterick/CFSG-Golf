module

public import CFSG.Assembly.OrderReductions.CharacterClassProducts
public import CFSG.Assembly.OrderReductions.TIInvolutionProducts

public section

namespace CFSG.OrderReductions.TIClassFunctionInduction

open CFSG.OrderReductions.InvolutionGraph

@[expose] noncomputable def zeroExtension {field group : Type*} [Field field] [Group group]
    (subgroup : Subgroup group) (function : subgroup → field) (element : group) : field := by
  classical
  exact if membership : element ∈ subgroup then function ⟨element, membership⟩ else 0

@[expose] noncomputable def inducedFunction {field group : Type*} [Field field] [Group group] [Fintype group]
    (subgroup : Subgroup group) (function : subgroup → field) (element : group) : field :=
  (Nat.card subgroup : field)⁻¹ *
    ∑ conjugator : group, zeroExtension subgroup function (conjugator * element * conjugator⁻¹)


end CFSG.OrderReductions.TIClassFunctionInduction
