module

public import CFSG.ClassicalInvolution.Uniform.UBranchExit
public import CFSG.ClassicalInvolution.Uniform.U3Datum

public section

namespace CFSG.ClassicalInvolution.Q3.Disc3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Uniform
open scoped MatrixGroups

section Stand

structure AscStand3 {G : Type} [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) :
    Prop where
  hyp : HypOmegaModU (.sl2 3 1) Ω
  below : CITBelowT (.sl2 3 1) (Nat.card G)
  ih : IH8T 3 1 (Nat.card G)
  aEmpty : ∀ J ∈ Ω, AEmpty Ω J
  mem : K ∈ Ω
  trans : ∀ J ∈ Ω, ∃ g : G, conjSub g K = J
  gen : (⨆ J ∈ Ω, J) = ⊤

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}


end Stand

section Forms

@[expose] def Thm6A3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand3 Ω K → 3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G → DEdgeless Ω →
      ConclusionD G

@[expose] def Thm7A3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand3 Ω K → 3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G →
      (∃ K' ∈ twinSet Ω K, K' ≠ K) → ¬ DConnected Ω → ConclusionD G

@[expose] def Thm8A3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K : Subgroup G),
    AscStand3 Ω K → 3 ≤ CFSG.Open.twoRank G → ¬ TwoSubgroupsFourGenerated G → ¬ DEdgeless Ω →
      (∀ K' ∈ twinSet Ω K, K' = K) → ¬ DConnected Ω → False


end Forms

section Branch

@[expose] def AscStand3OfBranch : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G),
    DBranchU 3 1 K z →
      AscStand3 (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) (satU (.sl2 3 1) K z)

theorem ascStand3OfBranch_of (hΩ : HypOmegaModDU 3 1) (hA : AEmptyDU 3 1)
    (hih : ∀ n : ℕ, CITBelowT (.sl2 3 1) n → IH8T 3 1 n) : AscStand3OfBranch := by
  intro G _ _ _ K z h
  have hK := h.member_satU
  exact
    { hyp := hΩ G K z h
      below := h.below
      ih := hih _ h.below
      aEmpty := hA G K z h
      mem := CoreAssembly.mem_conjClass_self _
      trans := fun J hJ => by
        obtain ⟨g, rfl⟩ := hJ
        exact ⟨g, rfl⟩
      gen := gen_conjClass _ hK.mem hK.ne_one }

theorem thm6DU_three_of (hs : AscStand3OfBranch) (h : Thm6A3) : Thm6DU 3 1 :=
  fun G _ _ _ K z hb hE =>
    h G _ (satU (.sl2 3 1) K z) (hs G K z hb) hb.rank hb.notFourGenerated hE

theorem thm7DU_three_of (hs : AscStand3OfBranch) (h : Thm7A3) : Thm7DU 3 1 :=
  fun G _ _ _ K z hb _ hT =>
    h G _ (satU (.sl2 3 1) K z) (hs G K z hb) hb.rank hb.notFourGenerated hT hb.dDisconnected

theorem thm8DU_three_of (hs : AscStand3OfBranch) (h : Thm8A3) : Thm8DU 3 1 :=
  fun G _ _ _ K z hb hE hT =>
    h G _ (satU (.sl2 3 1) K z) (hs G K z hb) hb.rank hb.notFourGenerated hE hT hb.dDisconnected

end Branch

end CFSG.ClassicalInvolution.Q3.Disc3
