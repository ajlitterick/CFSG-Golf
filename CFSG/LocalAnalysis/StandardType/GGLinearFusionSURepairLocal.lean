module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairPair
public import CFSG.LocalAnalysis.StandardType.GGSixAutStructurePSUHolds

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormConjHom primeFormConjHom_mk
  primeFormUnitary mem_primeFormUnitary)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)
open scoped commutatorElement

namespace SURepair

theorem commutator_le_left_of_le_normalizer {G : Type} [Group G] {T B : Subgroup G}
    (hBT : B ≤ Subgroup.normalizer (T : Set G)) : ⁅T, B⁆ ≤ T := by
  rw [Subgroup.commutator_le]
  intro t ht b hb
  rw [commutatorElement_def]
  have h1 : b * t⁻¹ * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hBT hb) _).mp (T.inv_mem ht)
  have h2 := T.mul_mem ht h1
  rwa [show t * (b * t⁻¹ * b⁻¹) = t * b * t⁻¹ * b⁻¹ by group] at h2

section Aut

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)
  {n : ℕ} {G : Type} [Group G]

theorem mem_primeFormUnitary_of_isJUnitary {A : GL (Fin n) K}
    (hA : InnerDiagSU.IsJUnitary (unitaryInvolution K 2 f) A) :
    A ∈ primeFormUnitary h ((AutPSU.gramJ n : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [mem_primeFormUnitary, AutPSU.coe_gramJ, ← SURep.conjTr_eq_bar h]
  exact hA


end Aut

end SURepair

section Inputs


end Inputs

end CFSG.StandardType
