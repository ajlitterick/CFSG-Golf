module

public import CFSG.ClassicalInvolution.Uniform.UBranchProof
public import CFSG.ClassicalInvolution.Q3.Q3PBranch

public section

namespace CFSG.ClassicalInvolution.Uniform

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
open scoped MatrixGroups

section Statements

variable (p f : ℕ) [Fact p.Prime]


@[expose] def Thm6DU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchU p f K z → DEdgeless (CoreAssembly.conjClass (satU (.sl2 p f) K z)) → ConclusionD G

@[expose] def Thm7DU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchU p f K z → ¬ DEdgeless (CoreAssembly.conjClass (satU (.sl2 p f) K z)) →
      (∃ K' ∈ twinSet (CoreAssembly.conjClass (satU (.sl2 p f) K z)) (satU (.sl2 p f) K z),
        K' ≠ satU (.sl2 p f) K z) → ConclusionD G

@[expose] def Thm8DU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchU p f K z → ¬ DEdgeless (CoreAssembly.conjClass (satU (.sl2 p f) K z)) →
      (∀ K' ∈ twinSet (CoreAssembly.conjClass (satU (.sl2 p f) K z)) (satU (.sl2 p f) K z),
        K' = satU (.sl2 p f) K z) → False

@[expose] def SmallDisconnectedDU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchU p f K z → ConclusionD G


end Statements

section Proofs

variable {p f : ℕ} [Fact p.Prime]


omit [Fact p.Prime] in
theorem smallDisconnectedDU_of_aschbacher (h6 : Thm6DU p f) (h7 : Thm7DU p f) (h8 : Thm8DU p f) :
    SmallDisconnectedDU p f := by
  intro G _ _ _ K z hb
  by_cases hE : DEdgeless (CoreAssembly.conjClass (satU (.sl2 p f) K z))
  · exact h6 G K z hb hE
  · by_cases hT : ∃ K' ∈ twinSet (CoreAssembly.conjClass (satU (.sl2 p f) K z))
        (satU (.sl2 p f) K z), K' ≠ satU (.sl2 p f) K z
    · exact h7 G K z hb hE hT
    · exact (h8 G K z hb hE fun K' hK' => by_contra fun hne => hT ⟨K', hK', hne⟩).elim


end Proofs

section Facades


end Facades

end CFSG.ClassicalInvolution.Uniform
