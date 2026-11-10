module

public import CFSG.LocalAnalysis.ComponentInitial.EmptyLayerCharTwo
public import CFSG.LocalAnalysis.ComponentInitial.FactorwiseFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBCentralQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBFixedCentralQuotientComponents

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

variable {G : Type*} [Group G]

theorem map_conj_eq_of_mem_normalizer {A : Subgroup G} {u : G}
    (hu : u ∈ normalizer (A : Set G)) : A.map (MulAut.conj u).toMonoidHom = A :=
  conjSub_eq_of_mem_normalizer hu

@[expose] def conjAut (A : Subgroup G) {u : G} (hu : u ∈ normalizer (A : Set G)) : MulAut A :=
  restrictAut (MulAut.conj u) A (map_conj_eq_of_mem_normalizer hu)

theorem coe_conjAut {A : Subgroup G} {u : G} (hu : u ∈ normalizer (A : Set G)) (x : A) :
    ((conjAut A hu x : A) : G) = u * x * u⁻¹ := rfl


section Factor

variable {A : Subgroup G} {u : G}


noncomputable abbrev quotientConjAut (hnorm : u ∈ normalizer (A : Set G)) :
    MulAut (A ⧸ center A) :=
  PerfectAutomorphisms.centerQuotientHom A (conjAut A hnorm)


theorem even_card_of_simple_nonabelian {S : Type*} [Group S] [Finite S] (hs : IsSimpleGroup S)
    (hnab : ∃ x y : S, x * y ≠ y * x) : Even (Nat.card S) := by
  rw [← Nat.not_odd_iff_even]
  intro hodd
  have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  obtain ⟨x, y, hxy⟩ := hnab
  have := hs
  exact hxy ((IsSimpleGroup.comm_iff_isSolvable).2 hsolv x y)


end Factor

section FactorImage


end FactorImage

section FactorConfiguration


end FactorConfiguration

end CFSG.LocalAnalysis.ComponentInitial
