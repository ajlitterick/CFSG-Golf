module

public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Conjugating finite-dimensional representations of subgroups

This file defines two ways to conjugate a finite-dimensional representation of a
subgroup.

* `FDRep.conj` conjugates a representation of a normal subgroup `A ⊆ G` by an
  element `g : G`; since `A` is normal, the result is again a representation of
  `A`.

* `FDRep.conjMap` conjugates a representation of an arbitrary subgroup `I ⊆ G`
  to a representation of the conjugate subgroup
  `I.map (MulAut.conj g).toMonoidHom`.

The file also contains helper lemmas for comparing the action of the conjugated
representation on elements of a normal subgroup contained in `I`.
-/

universe u v w

open CategoryTheory

namespace FDRep

/--
Conjugate a representation of a normal subgroup by an element of the ambient
group.

If `A ⊆ G` is normal and `σ` is a representation of `A`, then `conjNormal A σ g`
is the representation of `A` obtained by precomposing `σ` with the automorphism
of `A` induced by conjugation by `g`.
-/
@[expose] noncomputable def conjNormal {k : Type u} [CommRing k] {G : Type v} [Group G]
  (A : Subgroup G) [A.Normal] (σ : FDRep k A) (g : G) : FDRep k A :=
  FDRep.of (σ.ρ.comp (MulAut.conjNormal (H := A) g).toMonoidHom)

@[simp]
lemma conjNormal_rho_apply {k : Type u} [CommRing k] {G : Type v} [Group G]
    (A : Subgroup G) [A.Normal] (σ : FDRep k A) (g : G) (a : A) :
    (conjNormal (A := A) σ g).ρ a = σ.ρ ((MulAut.conjNormal (H := A) g) a) := rfl

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]

/--
Conjugate a representation of a subgroup to a representation of the conjugate
subgroup.

If `σ` is a representation of `I`, then `conjMap I g σ` is a representation of
`g I g⁻¹`, represented here as `I.map (MulAut.conj g).toMonoidHom`.
The action is obtained by transporting back along the subgroup equivalence
induced by `MulAut.conj g`.
-/
@[expose] noncomputable def conjMap
    (I : Subgroup G) (g : G) (σ : FDRep k I) :
    FDRep k (I.map (MulAut.conj g).toMonoidHom) := by
  let e : I ≃* I.map (MulAut.conj g).toMonoidHom :=
    (MulAut.conj g).subgroupMap I
  exact FDRep.of (σ.ρ.comp e.symm.toMonoidHom)

@[simp]
lemma conjMap_rho_apply
    (I : Subgroup G) (g : G)
    (σ : FDRep k I)
    (x : I.map (MulAut.conj g).toMonoidHom)
    (v : (FDRep.conjMap (k := k) I g σ)) :
    (FDRep.conjMap (k := k) I g σ).ρ x v =
      σ.ρ (((MulAut.conj g).subgroupMap I).symm x) v :=
  rfl


end FDRep
