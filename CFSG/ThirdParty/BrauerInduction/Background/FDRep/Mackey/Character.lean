module

public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Mackey.Basic
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Character.Basic
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Character.Orthogonality
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Character.Induced
public import CFSG.ThirdParty.BrauerInduction.Background.Fintype.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-! # Character computation for Mackey Hom terms

This file computes the dimensions of the Mackey Hom terms introduced in
`FDRep.Mackey.Basic` using character inner products.

The final result expresses

`finrank End(Ind_I^G σ)`

as a sum over double cosets of the dimensions of the corresponding Mackey Hom
terms. -/

open CategoryTheory BigOperators

universe u v

namespace FDRep

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]


/--
The character of the left Mackey restriction is the restriction of `σ.character`
through the left inclusion into `I`.
-/
@[simp] lemma char_mackeyLeftRes
    [Finite G]
    (I : Subgroup G) (σ : FDRep k I) (g : G)
    (h : mackeyIntersection I g) :
    (mackeyLeftRes (k := k) I σ g).character h
      =
    σ.character ⟨(h : G), h.2.1⟩ := by
  rfl

/--
The Mackey Hom-term dimension formula with the two restricted characters
expanded explicitly in terms of `σ.character`.
-/
@[simp] lemma char_mackeyConjRes
    [Finite G]
    (I : Subgroup G) (σ : FDRep k I) (g : G)
    (h : mackeyIntersection I g) :
    (mackeyConjRes (k := k) I σ g).character h
      =
    σ.character
      (((MulAut.conj g).subgroupMap I).symm
        ⟨(h : G), h.2.2⟩) := by
  change
    (FDRep.conjMap (k := k) I g σ).character
      ⟨(h : G), h.2.2⟩
      =
    σ.character
      (((MulAut.conj g).subgroupMap I).symm
        ⟨(h : G), h.2.2⟩)
  rfl


end FDRep
