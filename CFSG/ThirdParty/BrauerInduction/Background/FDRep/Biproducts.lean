module

public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Basic
public import Mathlib.RingTheory.Finiteness.Prod

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Biproducts of finite-dimensional representations

This file constructs binary and finite biproducts in `FDRep k G`.

The concrete binary biproduct is given by the product of the underlying modules,
with the product representation. We also provide linear equivalences describing
the underlying module of a biproduct and helper lemmas for morphisms into finite
biproducts.
-/

namespace FDRep

open CategoryTheory
open CategoryTheory.Limits

universe u v w wι

section BinaryBiproducts

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]


noncomputable instance instHasBinaryBiproductsFDRep :
  HasBinaryBiproducts (FDRep k G) := HasBinaryBiproducts.of_hasBinaryCoproducts

end BinaryBiproducts

section FiniteBiproducts

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

variable {ι : Type wι}

noncomputable instance instHasTerminal :
    HasTerminal (FDRep k G) := by
  apply HasZeroObject.hasTerminal

/--
The category `FDRep k G` has finite products.
-/
noncomputable instance instHasFiniteProducts :
    HasFiniteProducts (FDRep k G) :=
  hasFiniteProducts_of_has_binary_and_terminal

/--
The concrete product of two finite-dimensional representations.

The underlying module is `V × W`, and the action is the product action
`V.ρ.prod W.ρ`.
-/
@[expose] noncomputable def prod (V W : FDRep k G) : FDRep k G := by
  exact FDRep.of (Representation.prod V.ρ W.ρ)

@[simp]
lemma prod_ρ (V W : FDRep k G) :
    (FDRep.prod V W).ρ = Representation.prod V.ρ W.ρ := by
  rfl

@[simp]
lemma prod_ρ_apply (V W : FDRep k G) (g : G) (x : V × W) :
    (FDRep.prod V W).ρ g x =
      (V.ρ g x.1, W.ρ g x.2) := by
  rw [FDRep.prod_ρ]
  exact Representation.prod_apply_apply V.ρ W.ρ g x


/-- Helper: The underlying vector space of a biproduct is linearly equivalent to the product. -/
noncomputable def linearEquivBiprod (X Y : FDRep k G) :
    (Limits.biprod X Y).V.obj ≃ₗ[k] X.V.obj × Y.V.obj :=
  { toFun := fun v =>
      ((Limits.biprod.fst : X ⊞ Y ⟶ X).hom.hom v,
       (Limits.biprod.snd : X ⊞ Y ⟶ Y).hom.hom v)
    map_add' := fun x y => by
      simp only [map_add, Prod.mk_add_mk]
    map_smul' := fun c x => by
      simp only [LinearMap.map_smul, Prod.smul_mk]
      simp only [FGModuleCat.obj_carrier, RingHom.id_apply]
    invFun := fun ⟨x, y⟩ =>
      (Limits.biprod.inl : X ⟶ X ⊞ Y).hom.hom x +
      (Limits.biprod.inr : Y ⟶ X ⊞ Y).hom.hom y
    left_inv := by
      intro v
      have htotal :
          Limits.biprod.fst ≫ Limits.biprod.inl
            + Limits.biprod.snd ≫ Limits.biprod.inr
            =
          (𝟙 (X ⊞ Y) : X ⊞ Y ⟶ X ⊞ Y) :=
        Limits.biprod.total
      exact congrArg (fun f : X ⊞ Y ⟶ X ⊞ Y => f.hom.hom v)  htotal

    right_inv := fun ⟨x, y⟩ => by
      have h1 : (Limits.biprod.fst : X ⊞ Y ⟶ X).hom.hom
        ((Limits.biprod.inl : X ⟶ X ⊞ Y).hom.hom x) = x := by
        have h := Limits.biprod.inl_fst (X := X) (Y := Y)
        calc (Limits.biprod.fst : X ⊞ Y ⟶ X).hom.hom ((Limits.biprod.inl : X ⟶ X ⊞ Y).hom.hom x)
          _ = (Limits.biprod.inl ≫ Limits.biprod.fst : X ⟶ X).hom.hom x := rfl
          _ = (𝟙 X : X ⟶ X).hom.hom x := by rw [h]
          _ = x := rfl

      have h2 : (Limits.biprod.fst : X ⊞ Y ⟶ X).hom.hom
        ((Limits.biprod.inr : Y ⟶ X ⊞ Y).hom.hom y) = 0 := by
        have h := Limits.biprod.inr_fst (X := X) (Y := Y)
        calc (Limits.biprod.fst : X ⊞ Y ⟶ X).hom.hom ((Limits.biprod.inr : Y ⟶ X ⊞ Y).hom.hom y)
          _ = (Limits.biprod.inr ≫ Limits.biprod.fst : Y ⟶ X).hom.hom y := rfl
          _ = (0 : Y ⟶ X).hom.hom y := by rw [h]
          _ = 0 := rfl

      have h3 : (Limits.biprod.snd : X ⊞ Y ⟶ Y).hom.hom
        ((Limits.biprod.inl : X ⟶ X ⊞ Y).hom.hom x) = 0 := by
        have h := Limits.biprod.inl_snd (X := X) (Y := Y)
        calc (Limits.biprod.snd : X ⊞ Y ⟶ Y).hom.hom ((Limits.biprod.inl : X ⟶ X ⊞ Y).hom.hom x)
          _ = (Limits.biprod.inl ≫ Limits.biprod.snd : X ⟶ Y).hom.hom x := rfl
          _ = (0 : X ⟶ Y).hom.hom x := by rw [h]
          _ = 0 := rfl

      have h4 : (Limits.biprod.snd : X ⊞ Y ⟶ Y).hom.hom
        ((Limits.biprod.inr : Y ⟶ X ⊞ Y).hom.hom y) = y := by
        have h := Limits.biprod.inr_snd (X := X) (Y := Y)
        calc (Limits.biprod.snd : X ⊞ Y ⟶ Y).hom.hom ((Limits.biprod.inr : Y ⟶ X ⊞ Y).hom.hom y)
          _ = (Limits.biprod.inr ≫ Limits.biprod.snd : Y ⟶ Y).hom.hom y := rfl
          _ = (𝟙 Y : Y ⟶ Y).hom.hom y := by rw [h]
          _ = y := rfl

      ext
      · simp only [map_add, h1,h2, AddMonoid.add_zero x]
      · simp only [map_add, h3,h4, AddZeroClass.zero_add y]
  }

noncomputable def biprodIsoProd (V W : FDRep k G) :
    (V ⊞ W) ≅ (FDRep.prod (k:=k) (G:=G) V W) := by
  -- Use your existing linear equivalence
  let e := linearEquivBiprod (X := V) (Y := W)
  -- Use your helper to construct the FDRep iso from a LinearEquiv
  refine FDRep.isoOfLinearEquiv e (fun g => ?_)
  apply LinearMap.ext; intro x
  dsimp [FDRep.prod, Representation.prod]
  -- The target is a product (V × W), check components separately
  apply Prod.ext
  · -- 1. First component (V)
    -- This is exactly the commutativity of the first projection
    -- We need: ρ_V g (lin biprod.fst x) = lin biprod.fst ((V ⊞ W).ρ g x)
    exact LinearMap.congr_fun (FDRep.hom_comp_ρ Limits.biprod.fst g).symm x
  · -- 2. Second component (W)
    -- Similarly for the second projection
    exact LinearMap.congr_fun (FDRep.hom_comp_ρ Limits.biprod.snd g).symm x

/--
The category `FDRep k G` has finite biproducts.
-/
noncomputable instance instHasFiniteBiproducts :
    HasFiniteBiproducts (FDRep k G) := HasFiniteBiproducts.of_hasFiniteProducts

/--
The biproduct over the empty indexing type is a zero object.
-/
lemma IsZero_biproduct_empty
    (f : PEmpty → FDRep k G) : IsZero (⨁ f) := by
  refine ⟨?_, ?_⟩
  · intro X
    refine ⟨⟨biproduct.desc (fun i : PEmpty => PEmpty.elim i)⟩, ?_⟩
    intro g
    apply biproduct.hom_ext'
    intro i
    cases i
  · intro X
    refine ⟨⟨biproduct.lift (fun i : PEmpty => PEmpty.elim i)⟩, ?_⟩
    intro g
    apply biproduct.hom_ext
    intro i
    cases i


end FiniteBiproducts

section HomToBiproduct

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

variable {ι : Type wι} [Finite ι]


end HomToBiproduct

section finrank

variable {k : Type u} {G : Type v} [Field k] [Monoid G]

lemma finrank_biprod (X Y : FDRep k G) :
      (X ⊞ Y).finrank = X.finrank + Y.finrank := by
  have e := FDRep.linearEquivBiprod (X := X) (Y := Y)
  have h :
      (X ⊞ Y).finrank = Module.finrank k ( X.V.obj × Y.V.obj ) := LinearEquiv.finrank_eq e
  rw [h,Module.finrank_prod]

end finrank

section OptionBiproduct

variable {k : Type u} {G : Type v} [CommRing k] [Monoid G]

variable {ι : Type wι} [Finite ι]

/--
Adjoining one extra summand to a finite biproduct.

The biproduct over `Option ι`, with `none` corresponding to `S` and `some i`
corresponding to `K i`, is isomorphic to `S ⊞ ⨁ K`.
-/
@[expose] noncomputable def biproductOptionIso
    (S : FDRep k G) (K : ι → FDRep k G) :
    (S ⊞ Limits.biproduct K) ≅ Limits.biproduct (Option.rec S K) := by
  let F : Option ι → FDRep k G := @Option.rec ι (fun _ => FDRep k G) S K
  let fwd : S ⊞ Limits.biproduct K ⟶ Limits.biproduct F :=
    Limits.biprod.desc
      (Limits.biproduct.ι F none)
      (Limits.biproduct.desc (fun i => Limits.biproduct.ι F (some i)))
  let inv : Limits.biproduct F ⟶ S ⊞ Limits.biproduct K :=
    Limits.biproduct.desc (fun o => match o with
      | none   => Limits.biprod.inl
      | some i => Limits.biproduct.ι K i ≫ Limits.biprod.inr)
  refine Iso.mk fwd inv ?_ ?_  <;> dsimp [fwd, inv]
  · apply Limits.biprod.hom_ext'
    · rw [←Category.assoc, Limits.biprod.inl_desc]
      simp only [Limits.biproduct.ι_desc]
      rfl
    · rw [←Category.assoc, Limits.biprod.inr_desc]
      apply Limits.biproduct.hom_ext'; intro i
      rw [←Category.assoc, Limits.biproduct.ι_desc]
      rw [Limits.biproduct.ι_desc]
      rfl
  · apply Limits.biproduct.hom_ext'; intro o
    cases o with
    | none =>
      rw [←Category.assoc, Limits.biproduct.ι_desc]
      rw [Limits.biprod.inl_desc]
      rfl
    | some i =>
      rw [←Category.assoc, Limits.biproduct.ι_desc]
      rw [Category.assoc, Limits.biprod.inr_desc]
      rw [Limits.biproduct.ι_desc]
      rfl

end OptionBiproduct

end FDRep
