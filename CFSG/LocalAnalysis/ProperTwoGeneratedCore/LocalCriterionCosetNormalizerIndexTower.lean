module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexOrbit
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndexFixedOrbit

public section

namespace CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex

open CFSG.ShultStronglyClosedTI
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer

universe u

variable {G : Type u} [Group G]

theorem normalizer_index_tower (N D : Subgroup G) (u : G)
    (hinter : N ⊓ D = (N ⊓ Subgroup.centralizer ({u} : Set G)) ⊓ D) :
    D.relIndex N = (Subgroup.centralizer ({u} : Set G)).relIndex N *
      D.relIndex (N ⊓ Subgroup.centralizer ({u} : Set G)) := by
  let A : Subgroup G := N ⊓ Subgroup.centralizer ({u} : Set G)
  calc
    _ = (A ⊓ D).relIndex N := by rw [← hinter, Subgroup.inf_relIndex_left]
    _ = (A ⊓ D).relIndex A * A.relIndex N :=
      (Subgroup.relIndex_mul_relIndex (A ⊓ D) A N inf_le_left inf_le_left).symm
    _ = _ := by rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left, mul_comm]


theorem q_times_degree_sub_one_twoPower (q k : ℕ)
    (hq : ∃ a : ℕ, q = 2 ^ a) (hk : ∃ i : ℕ, k = q ^ i + 1) :
    ∃ a : ℕ, q * (k - 1) = 2 ^ a := by
  obtain ⟨a, rfl⟩ := hq
  obtain ⟨i, rfl⟩ := hk
  refine ⟨a + a * i, ?_⟩
  rw [Nat.add_sub_cancel, ← pow_mul, ← pow_add]

end CFSG.ProperTwoGeneratedCore.LocalCriterionCosetNormalizerIndex
