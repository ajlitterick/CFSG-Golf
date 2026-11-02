module

public import CFSG.ClassicalInvolution.SmallCases.NDBE2Frame
import CFSG.ClassicalInvolution.SmallCases.NDB5Sec
import CFSG.ClassicalInvolution.SmallCases.NDB5eG2

public section

namespace CFSG.ClassicalInvolution.NDB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.ExactLayer
open CFSG.Assembly.LowTwoRank

local notation "𝒞" => Generic.CoreAssembly.conjClass

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {K : Subgroup G} {z : G}

namespace ExoticLift

variable {C : ExoticCtx p f K z} (L : ExoticLift C)

abbrev B : Subgroup G := Subgroup.closure ({z, L.t, L.z'} : Set G)

theorem z_mem_B : z ∈ L.B := Subgroup.subset_closure (Set.mem_insert _ _)

theorem t_mem_B : L.t ∈ L.B :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))

theorem z'_mem_B : L.z' ∈ L.B :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem B_elem : IsElemAbelian 2 L.B :=
  L.frameData₁.isElemAbelian C.hS.odd C.X.hΩ

theorem B_card : Nat.card L.B = 8 :=
  L.frameData₁.natCard_eight C.hS.odd C.hS.five C.X.hΩ

theorem hyp51At_z : Hyp51At L.B z := by
  have hz1 : z ≠ 1 := C.X.hKz.ne_one
  have hmov : ∀ M : Subgroup (OddQuot z), CFSG.IsComponent M → MovedByAll L.B z M →
      M = (C.psi C.i₁).range := fun M hM hm =>
    S.moved_eq_range C.hS.odd C.hS.five C.X.hs C.D L.B_elem L.z_mem_B hz1 L.t_mem_B
      L.uJ.ne_one L.t_ne_z (fun hb => ⟨L.τ₁, L.htbar.symm⟩) hM hm
  refine ⟨fun M₁ M₂ h₁ h₂ m₁ m₂ => (hmov M₁ h₁ m₁).trans (hmov M₂ h₂ m₂).symm, ?_⟩
  intro M hM hm
  rw [hmov M hM hm]
  have hset : ({L.t, L.z', z} : Set G) = {z, L.t, L.z'} := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hA : IsElemAbelian 2 (Subgroup.closure ({L.t, L.z', z} : Set G)) := by
    rw [hset]
    exact L.B_elem
  have h := Alpha.alpha_g2d4 C.hS.odd C.hS.five hA L.uJ.ne_one L.uK'.ne_one L.t_ne_z'
    C.X.hs.normalizes C.D C.i₁ C.tag₁ (fun hb => ⟨L.τ₁, L.htbar.symm⟩)
    (fun hb => ⟨L.τ₂, L.hz'bar.symm⟩)
  rwa [hset] at h

end ExoticLift

end CFSG.ClassicalInvolution.NDB
