module

public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.ConjMap
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Basic
public import CFSG.ThirdParty.BrauerInduction.Background.Group.DoubleCoset

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Mackey summands for induced representations

This file defines the representation-theoretic summands that occur in the Mackey
decomposition for `Res Ind`.

For a subgroup `I ≤ G`, a representation `σ` of `I`, and an element `g : G`, the
relevant subgroup is

`I ∩ gIg⁻¹`.

There are two representations of this subgroup: the restriction of `σ`, and the
restriction of the conjugate representation. The Hom space between these two
representations is the Mackey Hom term associated to `g`.

The character computations for these terms are developed in
`FDRep.Mackey.Character`.
-/

open CategoryTheory

universe u v

namespace FDRep

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/-
These two helpers are good general `FDRep` API. If they already exist in your
basic file, delete the local versions below and use the global names.
-/

/--
The conjugate subgroup `gIg⁻¹`.
-/
abbrev mackeyConjSubgroup (I : Subgroup G) (g : G) : Subgroup G :=
  I.map (MulAut.conj g).toMonoidHom

/--
The Mackey intersection `I ∩ gIg⁻¹`.
-/
abbrev mackeyIntersection (I : Subgroup G) (g : G) : Subgroup G :=
  I ⊓ mackeyConjSubgroup I g

/--
The restriction of `σ` to the Mackey intersection `I ∩ gIg⁻¹` through the left
inclusion into `I`.
-/
noncomputable abbrev mackeyLeftRes
    (I : Subgroup G) (σ : FDRep k I) (g : G) :
    FDRep k (mackeyIntersection I g) :=
  FDRep.of (σ.ρ.comp (Subgroup.inclusion inf_le_left))

/--
The restriction of the conjugate representation `σᵍ` to the Mackey intersection
`I ∩ gIg⁻¹`.
-/
noncomputable abbrev mackeyConjRes
    (I : Subgroup G) (σ : FDRep k I) (g : G) :
    FDRep k (mackeyIntersection I g) :=
  let σg := FDRep.conjMap (k := k) I g σ
  FDRep.of (σg.ρ.comp (Subgroup.inclusion inf_le_right))


end FDRep
