module

public import CFSG.Quasithin.Background.F918P1
public import CFSG.Quasithin.Background.PGroupIrrTrivial
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A1cModuleHomog

public section

namespace CFSG.Quasithin.RonanD34

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {W : Type} [CommGroup W]


section Basic

variable {M Mp T : Subgroup (MulAut W)} {V : Subgroup W}


end Basic

section Coprime

variable {G : Type*} [Group G]


end Coprime

section Clause1

variable [Finite W] {M Mp T : Subgroup (MulAut W)} {V : Subgroup W}


end Clause1

section Clause2

variable [Finite W] {M Mp T : Subgroup (MulAut W)} {V : Subgroup W}


end Clause2

section Burnside


end Burnside

section Helpers

variable {G : Type*} [Group G]


end Helpers

section PointwiseSmul

open scoped Pointwise


end PointwiseSmul

section AutSubLemmas

variable {Mp T : Subgroup (MulAut W)} {U : Subgroup W}


end AutSubLemmas

section Clause1b

variable [Finite W] {M Mp T : Subgroup (MulAut W)} {V : Subgroup W}


end Clause1b

section SemisimpleHomog

open scoped Pointwise

section Abstract

variable {A : Type*} [Group A] {T : Type*} [Group T] {Q : Type*} [CommGroup Q]
  [MulDistribMulAction A Q] [MulDistribMulAction T Q]


end Abstract

section Semisimple

variable {G : Type*} [Group G] {V : Type*} [CommGroup V] [MulDistribMulAction G V]
  {X T : Subgroup G} {S I : Subgroup V}


end Semisimple


end SemisimpleHomog

section Clause4

variable [Finite W]


end Clause4

section FStar

variable {G : Type*} [Group G] [Finite G]


theorem isComponent_map_subtype_of_normal {A : Type*} [Group A] {W : Subgroup A} (hW : W.Normal)
    {K : Subgroup ↥W} (hK : CFSG.IsComponent K) : CFSG.IsComponent (K.map W.subtype) :=
  ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (K.equivMapOfInjective W.subtype W.subtype_injective) hK.1,
    hK.2.trans' hW.isSubnormal⟩

theorem map_layer_le_layer_of_normal {A : Type*} [Group A] {W : Subgroup A} (hW : W.Normal) :
    (CFSG.layer ↥W).map W.subtype ≤ CFSG.layer A := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  rw [← Subgroup.map_le_iff_le_comap]
  exact CFSG.LocalCores.component_le_layer (isComponent_map_subtype_of_normal hW hK)


end FStar


section CommuteOn


end CommuteOn

section Clause1V


end Clause1V

section Clause5


end Clause5

section Clause36


end Clause36

end CFSG.Quasithin.RonanD34
