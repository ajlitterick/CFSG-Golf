module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Class

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Conj

theorem sup_centralizer_conj_eq_top_iff {G : Type*} [Group G] (g u v : G) :
    Subgroup.centralizer ({g * u * g⁻¹} : Set G) ⊔ Subgroup.centralizer ({g * v * g⁻¹} : Set G) =
        ⊤ ↔
      Subgroup.centralizer ({u} : Set G) ⊔ Subgroup.centralizer ({v} : Set G) = ⊤ := by
  rw [← conjSub_centralizer_singleton_g2d4, ← conjSub_centralizer_singleton_g2d4,
    ← Subgroup.map_sup]
  constructor
  · intro h
    exact Subgroup.map_injective (MulAut.conj g).injective
      (h.trans (Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective).symm)
  · intro h
    rw [h]
    exact Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

end Conj

section Ambient

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem torusGroup_mul_comm {t s : ModGL Tag.G2 F} (ht : t ∈ torusGroup Tag.G2 F)
    (hs : s ∈ torusGroup Tag.G2 F) : t * s = s * t := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨c, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hs
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]


end Ambient

section Model


end Model

end CFSG.ClassicalInvolution.G2D4Models
