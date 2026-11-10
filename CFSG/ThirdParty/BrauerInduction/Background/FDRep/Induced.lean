module

public import Mathlib.RepresentationTheory.FiniteIndex
public import Mathlib.CategoryTheory.Adjunction.Unique
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Res

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Induction and coinduction of finite-dimensional representations

This file defines induction and coinduction for `FDRep`.

Main definitions:

* `FDRep.indHom`: induction along a group homomorphism;
* `FDRep.ind`: induction from a subgroup;
* `FDRep.coindHom`: coinduction along a group homomorphism;
* `FDRep.coind`: coinduction from a subgroup;
* `FDRep.indIsoCoind`: the finite-group isomorphism between induction and
  coinduction;
* Frobenius reciprocity for induction and restriction;
* induction from the top subgroup;
* transitivity of induction.

Several subgroup-level statements require the ambient group to be in the same
universe as the coefficient ring.  This reflects the universe shape of Mathlib
`FDRep`: the carrier of an object of `FDRep k G` lives in the coefficient
universe, while induced and coinduced `Rep`s are built from the target group.

-/

universe u v v' w

open CategoryTheory

namespace FDRep

/-! ### Induction along an arbitrary group homomorphism -/

section HomInduction

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]
variable {H : Type u} [Group H]

/--
Induction of a finite-dimensional representation along a group homomorphism.

The target group is assumed finite so that the induced representation has
finitely generated underlying module.
-/
@[expose] noncomputable def indHom [Finite H]
    (φ : G →* H)
    (σ : FDRep k G) :
    FDRep k H := by
  let A : Rep k G := asRep σ
  let τind : Rep k H := Rep.ind φ A
  have h_fin_τ : Module.Finite k τind.V := by
    letI : Fintype H := Fintype.ofFinite H
    haveI : Module.Finite k A.V := by
      change Module.Finite k σ
      infer_instance
    exact Module.Finite.of_surjective
      (Representation.Coinvariants.mk _) (Submodule.mkQ_surjective _)
  haveI : Module.Finite k τind.V := h_fin_τ
  exact FDRep.of τind.ρ

@[simp]
lemma forget₂_obj_indHom [Finite H]
    (φ : G →* H)
    (σ : FDRep k G) :
    (forget₂ (FDRep k H) (Rep k H)).obj (indHom φ σ) =
      Rep.ind φ (asRep σ) := by
  rfl

/-- Induction along a homomorphism on morphisms. -/
@[expose] noncomputable def indHomMap [Finite H]
    (φ : G →* H)
    {A B : FDRep k G}
    (f : A ⟶ B) :
    indHom φ A ⟶ indHom φ B :=
  FDRep.forget₂HomLinearEquiv (indHom φ A) (indHom φ B)
    (Rep.indMap φ ((forget₂ (FDRep k G) (Rep k G)).map f))

@[simp]
lemma forget₂_map_indHomMap [Finite H]
    (φ : G →* H)
    {A B : FDRep k G}
    (f : A ⟶ B) :
    (forget₂ (FDRep k H) (Rep k H)).map (indHomMap φ f) =
      Rep.indMap φ ((forget₂ (FDRep k G) (Rep k G)).map f) := by
  rfl

/-- Induction along a homomorphism as a functor. -/
@[expose, simps obj map]
noncomputable def indHomFunctor [Finite H]
    (φ : G →* H) :
    FDRep k G ⥤ FDRep k H where
  obj A := indHom φ A
  map f := indHomMap φ f
  map_id X := by
    let U_G : FDRep k G ⥤ Rep k G := forget₂ (FDRep k G) (Rep k G)
    let U_H : FDRep k H ⥤ Rep k H := forget₂ (FDRep k H) (Rep k H)
    let F : Rep k G ⥤ Rep k H := Rep.indFunctor k φ
    apply U_H.map_injective
    change F.map (U_G.map (𝟙 X)) = 𝟙 (F.obj (U_G.obj X))
    simp only [CategoryTheory.Functor.map_id, F.map_id (U_G.obj X)]
  map_comp {X Y Z} f g := by
    let U_G : FDRep k G ⥤ Rep k G := forget₂ (FDRep k G) (Rep k G)
    let U_H : FDRep k H ⥤ Rep k H := forget₂ (FDRep k H) (Rep k H)
    let F : Rep k G ⥤ Rep k H := Rep.indFunctor k φ
    apply U_H.map_injective
    change F.map (U_G.map (f ≫ g)) = F.map (U_G.map f) ≫ F.map (U_G.map g)
    rw [Functor.map_comp]
    exact F.map_comp (U_G.map f) (U_G.map g)

end HomInduction


/-! ### Subgroup induction as a special case -/

section SubgroupInduction

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

/-- Induction from a subgroup, defined a special case of `indHom`. -/
noncomputable abbrev ind [Finite G] (H : Subgroup G) (σ : FDRep k H) : FDRep k G :=
  indHom H.subtype σ


/-- Induction from a subgroup as a functor. -/
@[simps!]
noncomputable abbrev indFunctor [Finite G] (H : Subgroup G) : FDRep k H ⥤ FDRep k G :=
  indHomFunctor H.subtype

@[simp]
lemma forget₂_obj_ind [Finite G] (H : Subgroup G) (σ : FDRep k H) :
    (forget₂ (FDRep k G) (Rep k G)).obj (ind H σ) =
      Rep.ind H.subtype (asRep σ) := by
  rfl


end SubgroupInduction

section HomCoinduction

variable {k : Type u} [CommRing k] [IsNoetherianRing k]
variable {G : Type v} [Group G]
variable {H : Type u} [Group H]

/--
Coinduction of a finite-dimensional representation along a group homomorphism.

The target group is assumed finite, and the coefficient ring is assumed
Noetherian so that the coinduced representation, realized as a submodule of a
finite product, is again finitely generated.
-/
noncomputable abbrev coindHom [Finite H]
    (φ : G →* H)
    (σ : FDRep k G) :
    FDRep k H := by
  let A : Rep k G := asRep σ
  let τcoind : Rep k H := Rep.coind φ A

  have h_fin_τ : Module.Finite k τcoind.V := by
    letI : Fintype H := Fintype.ofFinite H

    haveI : Module.Finite k A.V := by
      change Module.Finite k σ
      infer_instance

    -- The ambient function space is finite as `H` is finite.
    haveI : Module.Finite k (H → A.V) :=
      Module.Finite.pi_iff.mpr fun _ => inferInstance

    -- The coinduced space is a submodule of this finite module.
    exact Module.Finite.of_injective
      (Submodule.subtype (Representation.coindV φ A.ρ))
      (by
        intro x y h
        exact Subtype.ext h)

  haveI : Module.Finite k τcoind.V := h_fin_τ
  exact FDRep.of τcoind.ρ

@[simp]
lemma forget₂_obj_coindHom [Finite H]
    (φ : G →* H)
    (σ : FDRep k G) :
    (forget₂ (FDRep k H) (Rep k H)).obj (coindHom φ σ) =
      Rep.coind φ (asRep σ) := by
  rfl

/-- Coinduction along a homomorphism on morphisms. -/
@[expose] noncomputable def coindHomMap [Finite H]
    (φ : G →* H)
    {A B : FDRep k G}
    (f : A ⟶ B) :
    coindHom φ A ⟶ coindHom φ B :=
  FDRep.forget₂HomLinearEquiv (coindHom φ A) (coindHom φ B)
    (Rep.coindMap φ ((forget₂ (FDRep k G) (Rep k G)).map f))

@[simp]
lemma forget₂_map_coindHomMap [Finite H]
    (φ : G →* H)
    {A B : FDRep k G}
    (f : A ⟶ B) :
    (forget₂ (FDRep k H) (Rep k H)).map (coindHomMap φ f) =
      Rep.coindMap φ ((forget₂ (FDRep k G) (Rep k G)).map f) := by
  rfl

/-- Coinduction along a homomorphism as a functor. -/
@[expose, simps obj map]
noncomputable def coindHomFunctor [Finite H]
    (φ : G →* H) :
    FDRep k G ⥤ FDRep k H where
  obj A := coindHom φ A
  map f := coindHomMap φ f
  map_id X := by
    let U_G : FDRep k G ⥤ Rep k G := forget₂ (FDRep k G) (Rep k G)
    let U_H : FDRep k H ⥤ Rep k H := forget₂ (FDRep k H) (Rep k H)
    let F : Rep k G ⥤ Rep k H := Rep.coindFunctor k φ
    apply U_H.map_injective
    change F.map (U_G.map (𝟙 X)) = 𝟙 (F.obj (U_G.obj X))
    simp only [CategoryTheory.Functor.map_id, F.map_id (U_G.obj X)]
  map_comp {X Y Z} f g := by
    let U_G : FDRep k G ⥤ Rep k G := forget₂ (FDRep k G) (Rep k G)
    let U_H : FDRep k H ⥤ Rep k H := forget₂ (FDRep k H) (Rep k H)
    let F : Rep k G ⥤ Rep k H := Rep.coindFunctor k φ
    apply U_H.map_injective
    change F.map (U_G.map (f ≫ g)) = F.map (U_G.map f) ≫ F.map (U_G.map g)
    rw [Functor.map_comp]
    exact F.map_comp (U_G.map f) (U_G.map g)

end HomCoinduction

/-! ### Subgroup coinduction as a special case -/

section SubgroupCoinduction

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

/-- Coinduction from a subgroup, defined as a special case of `coindHom`. -/
noncomputable abbrev coind [Finite G] [IsNoetherianRing k]
    (H : Subgroup G) (σ : FDRep k H) : FDRep k G :=
  coindHom H.subtype σ


/-- Coinduction from a subgroup as a functor. -/
@[simps!]
noncomputable abbrev coindFunctor [Finite G] [IsNoetherianRing k]
    (H : Subgroup G) : FDRep k H ⥤ FDRep k G :=
  coindHomFunctor H.subtype

@[simp]
lemma forget₂_obj_coind [Finite G] [IsNoetherianRing k]
    (H : Subgroup G) (σ : FDRep k H) :
    (forget₂ (FDRep k G) (Rep k G)).obj (coind H σ) =
      Rep.coind H.subtype (asRep σ) := by
  rfl


end SubgroupCoinduction

section indIsoCoind

variable {k : Type u} [CommRing k] [IsNoetherianRing k]
variable {G : Type u} [Group G]

open Classical in
/--
The isomorphism `Ind ≅ Coind` in `FDRep` for finite groups.
-/
@[expose] noncomputable def indIsoCoind [Finite G]
    (I : Subgroup G)
    (σ : FDRep k I) :
    FDRep.ind I σ ≅ FDRep.coind I σ := by
  letI : DecidableRel (QuotientGroup.rightRel I) := Classical.decRel _
  haveI : I.FiniteIndex := by infer_instance

  let A : Rep k I := asRep σ
  let e : Rep.ind I.subtype A ≅ Rep.coind I.subtype A :=
    Rep.indCoindIso (S := I) A

  refine
    { hom :=
        FDRep.forget₂HomLinearEquiv
          (FDRep.ind I σ) (FDRep.coind I σ) e.hom
      inv :=
        FDRep.forget₂HomLinearEquiv
          (FDRep.coind I σ) (FDRep.ind I σ) e.inv
      hom_inv_id := ?_
      inv_hom_id := ?_ }

  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change e.hom ≫ e.inv = 𝟙 (Rep.ind I.subtype A)
    exact e.hom_inv_id

  · apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    change e.inv ≫ e.hom = 𝟙 (Rep.coind I.subtype A)
    exact e.inv_hom_id

end indIsoCoind

section HomFrobeniusReciprocity

variable {k : Type u} [CommRing k]
variable {G : Type v} [Group G]
variable {H : Type u} [Group H] [Finite H]

/--
Frobenius reciprocity for induction and pullback along a group homomorphism.

For `φ : G →* H`, morphisms from the induced representation `indHom φ σ` to
`ρ` correspond linearly to morphisms from `σ` to the pulled-back representation
`comap φ ρ`.
-/
@[expose] noncomputable def indHomComapEquiv
    (φ : G →* H)
    (σ : FDRep k G)
    (ρ : FDRep k H) :
    (indHom φ σ ⟶ ρ) ≃ₗ[k]
      (σ ⟶ comap (G := H) (H := G) φ ρ) := by
  let UG : FDRep k G ⥤ Rep k G := forget₂ (FDRep k G) (Rep k G)
  let UH : FDRep k H ⥤ Rep k H := forget₂ (FDRep k H) (Rep k H)

  let A : Rep k G := UG.obj σ
  let B : Rep k H := UH.obj ρ
  let ρres : FDRep k G := comap (G := H) (H := G) φ ρ

  let e₁ : (indHom φ σ ⟶ ρ) ≃ₗ[k] (Rep.ind φ A ⟶ B) :=
    (FDRep.forget₂HomLinearEquiv (indHom φ σ) ρ).symm

  let e₂ : (Rep.ind φ A ⟶ B) ≃ₗ[k] (A ⟶ Rep.res φ B) :=
    Rep.indResHomEquiv φ A B

  let e₃ : (A ⟶ Rep.res φ B) ≃ₗ[k] (σ ⟶ ρres) :=
    FDRep.forget₂HomLinearEquiv σ ρres

  exact e₁.trans (e₂.trans e₃)

end HomFrobeniusReciprocity

/-! ### Frobenius reciprocity for subgroup induction -/

section SubgroupFrobeniusReciprocity

variable {k : Type u} [CommRing k]
variable {G : Type u} [Group G] [Finite G]

variable (I : Subgroup G)

/--
Frobenius reciprocity for induction from a subgroup.
-/
@[expose] noncomputable def indResHomEquiv
    (σ : FDRep k I) (ρ : FDRep k G) :
    (FDRep.ind I σ ⟶ ρ) ≃ₗ[k] (σ ⟶ FDRep.res ρ I) :=
  indHomComapEquiv
    (G := I) (H := G)
    I.subtype σ ρ

@[expose] noncomputable def indResUnit (σ : FDRep k I) :
    σ ⟶ res (G := G) (FDRep.ind (G := G) I σ) I :=
  FDRep.indResHomEquiv (I := I) σ (FDRep.ind (G := G) I σ) (𝟙 _)

@[expose] noncomputable def indResCounit (ρ : FDRep k G) :
    FDRep.ind (G := G) I
        (res (G := G) ρ I) ⟶ ρ :=
  (FDRep.indResHomEquiv (I := I)
      (res (G := G) ρ I) ρ).symm (𝟙 _)

@[simp]
lemma indResHomEquiv_id
    (σ : FDRep k I) :
    FDRep.indResHomEquiv I σ (FDRep.ind I σ) (𝟙 _) =
      FDRep.indResUnit I σ := by
  rfl

@[simp]
lemma indResHomEquiv_symm_id
    (ρ : FDRep k G) :
    (FDRep.indResHomEquiv I (FDRep.res ρ I) ρ).symm (𝟙 _) =
      FDRep.indResCounit I ρ := by
  rfl


@[simp]
lemma forget₂_map_indResHomEquiv
    (σ : FDRep k I) (ρ : FDRep k G)
    (f : FDRep.ind I σ ⟶ ρ) :
    (forget₂ (FDRep k I) (Rep k I)).map
        (FDRep.indResHomEquiv (k := k) (G := G) I σ ρ f)
      =
    Rep.indResHomEquiv I.subtype
      ((forget₂ (FDRep k I) (Rep k I)).obj σ)
      ((forget₂ (FDRep k G) (Rep k G)).obj ρ)
      ((forget₂ (FDRep k G) (Rep k G)).map f) := by
  rfl

@[simp]
lemma forget₂_map_indResHomEquiv_symm
    (σ : FDRep k I) (ρ : FDRep k G)
    (f : σ ⟶ FDRep.res ρ I) :
    (forget₂ (FDRep k G) (Rep k G)).map
        ((FDRep.indResHomEquiv (k := k) (G := G) I σ ρ).symm f)
      =
    (Rep.indResHomEquiv I.subtype
      ((forget₂ (FDRep k I) (Rep k I)).obj σ)
      ((forget₂ (FDRep k G) (Rep k G)).obj ρ)).symm
      ((forget₂ (FDRep k I) (Rep k I)).map f) := by
  rfl

end SubgroupFrobeniusReciprocity

section top


end top

section transitivity


end transitivity

section top


section top


end top


end top

end FDRep
