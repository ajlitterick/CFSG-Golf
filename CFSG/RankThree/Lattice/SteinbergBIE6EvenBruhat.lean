module

public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBridge
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.RankThree.Lattice.SteinbergBIGenBruhat

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 CFSG.LieType.AlgebraicGroups
open scoped Pointwise


namespace E6EvenFixedRootDatum

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω] (D : E6EvenFixedRootDatum Ω)

theorem orbitMap_mul {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits)
    (A B : SL2 (D.orbitField O)) : D.orbitMap O (A * B) = D.orbitMap O A * D.orbitMap O B := by
  obtain ⟨σ, -, h⟩ := D.exists_orbitMap_eq_gen hO
  rw [h, h, h, map_mul]
  exact D.gen.orbitMap_mul (D.mem_gen_orbits.2 hO) _ _


theorem orbitMap_mem_orbitGroup {O : Set (Fin Tag.E6.rank → ℤ)} (hO : O ∈ D.orbits)
    (A : SL2 (D.orbitField O)) : D.orbitMap O A ∈ D.orbitGroup := by
  obtain ⟨σ, -, h⟩ := D.exists_orbitMap_eq_gen hO
  rw [h, ← D.gen_orbitGroup]
  exact D.gen.orbitMap_mem_orbitGroup (D.mem_gen_orbits.2 hO) _


theorem finite_fixedGroup : Finite D.fixedGroup := by
  have := D.gen.finite_fixedGroup
  rw [← D.gen_fixedGroup]
  exact Finite.of_equiv _ (D.gen.fixedGroup.equivMapOfInjective _
    (adjointGroup Tag.E6 Ω).subtype_injective).toEquiv

theorem orbitGroup_le_fixedGroup : D.orbitGroup ≤ D.fixedGroup := by
  rw [← D.gen_orbitGroup, ← D.gen_fixedGroup]
  intro g hg
  exact ⟨⟨g, D.gen.orbitGroup_le_adjointGroup hg⟩,
    D.gen.orbitGroupC_le_fixedGroup (D.gen.mk_mem_orbitGroupC hg), rfl⟩


theorem coe_fixedGroup_eq_mul :
    (D.fixedGroup : Set (ModGL Tag.E6 Ω)) =
      (D.fixedTorus : Set (ModGL Tag.E6 Ω)) * (D.orbitGroup : Set (ModGL Tag.E6 Ω)) := by
  have h := congrArg (fun s => (adjointGroup Tag.E6 Ω).subtype '' s) D.gen.coe_fixedGroup_eq_mul
  simp only [Set.image_mul] at h
  rw [← D.gen_fixedGroup, ← D.gen_fixedTorus, Subgroup.coe_map, Subgroup.coe_map, h]
  congr 1
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← D.gen_orbitGroup]
    exact Subgroup.mem_subgroupOf.1 hx
  · intro hg
    rw [SetLike.mem_coe, ← D.gen_orbitGroup] at hg
    exact ⟨⟨g, D.gen.orbitGroup_le_adjointGroup hg⟩, D.gen.mk_mem_orbitGroupC hg, rfl⟩

theorem commutator_fixedGroup_le : ⁅D.fixedGroup, D.fixedGroup⁆ ≤ D.orbitGroup := by
  rw [← D.gen_fixedGroup, ← Subgroup.map_commutator]
  refine (Subgroup.map_mono D.gen.commutator_fixedGroup_le).trans ?_
  rintro _ ⟨x, hx, rfl⟩
  rw [← D.gen_orbitGroup]
  exact Subgroup.mem_subgroupOf.1 hx


end E6EvenFixedRootDatum

