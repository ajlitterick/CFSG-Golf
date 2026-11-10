module

public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Mackey.Character
public import CFSG.ThirdParty.BrauerInduction.Background.LinearChar.Eigenspace

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG


/-!
# Mackey theory for induced linear characters

This file specializes the Mackey character computation to representations
induced from inertia groups of linear characters.

Let `A` be an abelian normal subgroup of `G`, let `ψ : A →* kˣ`, and let
`I` be the inertia subgroup of `ψ`. If a representation `σ` of `I` embeds into
the `ψ`-eigenspace of a representation `ρ`, then all Mackey terms outside the
identity double coset vanish. Consequently the endomorphism ring of
`Ind_I^G σ` has dimension one when `σ` is simple.
-/

open CategoryTheory BigOperators

universe u v

namespace FDRep


end FDRep
