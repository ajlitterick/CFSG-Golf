module

public import CFSG.ClassicalInvolution.Q3.Q3NTLemmaD
public import CFSG.ClassicalInvolution.Q3.Q3WAComp

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NL

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

section Elements

variable {G : Type} [Group G]


end Elements

section Involutions

variable {G : Type} [Group G] [Finite G]


end Involutions

section Nonabelian

variable {G : Type} [Group G] [Finite G]


end Nonabelian

section Indep

variable {G : Type} [Group G]

@[expose] def IndepModOdd (Ω : Set (Subgroup G)) (z n₁ n₂ : G) : Prop :=
  n₁⁻¹ * z ∉ oddCoreIn (locLayer Ω z) ∧ n₂⁻¹ * z ∉ oddCoreIn (locLayer Ω z) ∧
    n₁⁻¹ * n₂ ∉ oddCoreIn (locLayer Ω z) ∧ (n₁ * n₂)⁻¹ * z ∉ oddCoreIn (locLayer Ω z)


theorem IndepModOdd.ne {Ω : Set (Subgroup G)} {z n₁ n₂ : G} (h : IndepModOdd Ω z n₁ n₂) :
    n₁ ≠ z ∧ n₂ ≠ z ∧ n₁ ≠ n₂ ∧ n₁ * n₂ ≠ z :=
  ⟨fun e => h.1 (by rw [e, inv_mul_cancel]; exact Subgroup.one_mem _),
    fun e => h.2.1 (by rw [e, inv_mul_cancel]; exact Subgroup.one_mem _),
    fun e => h.2.2.1 (by rw [e, inv_mul_cancel]; exact Subgroup.one_mem _),
    fun e => h.2.2.2 (by rw [e, inv_mul_cancel]; exact Subgroup.one_mem _)⟩

end Indep

section GroupLemma


end GroupLemma

section Branch


structure NTCommon3 {G : Type} [Group G] [Finite G] (K : Subgroup G) (z : G) : Prop where
  nonab : ∃ a b : G, a * b ≠ b * a
  cls : IsClassicalMember3 K z
  below : CIT3Below (Nat.card G)
  rank : 3 ≤ twoRank G
  large : ¬ TwoSubgroupsFourGenerated G
  delta : DeltaConnected K


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}

theorem NTCommon3.inClass (h : NTCommon3 K z) : InClass3 (conjClass3 K) :=
  inClass3_conjugates h.cls


end Branch

section Components


end Components

end CFSG.ClassicalInvolution.Q3.Q3NL
