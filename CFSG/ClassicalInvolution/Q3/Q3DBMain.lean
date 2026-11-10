module

public import CFSG.ClassicalInvolution.Q3.Q3DBChain
public import CFSG.ClassicalInvolution.Uniform.UBranchExit

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3DB

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Uniform


theorem deltaConnected_of_oddCentralizerFree {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G}
    (hz : IsClassicalMemberU (.sl2 3 1) K z) (hBelow : CITBelowT (.sl2 3 1) (Nat.card G))
    (hW : Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥)
    (hD : DConnected (CoreAssembly.conjClass (satU (.sl2 3 1) K z))) :
    CFSG.ClassicalInvolution.DeltaConnected K := by
  rw [satU_three_eq_of_oddCentralizerFree hW] at hD
  exact deltaConnected_of_dConnected_of_oddCentralizerFree hnab (hz.toQ3 (by norm_num)) hW
    ((citBelowT_three_iff (p := 3) (f := 1) (by norm_num) _).mp hBelow) hD


@[expose] def BootNoTripleD3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ x y : G, x * y ≠ y * x) →
    ∀ (K : Subgroup G) (z : G), IsClassicalMemberU (.sl2 3 1) K z →
      CITBelowT (.sl2 3 1) (Nat.card G) → 3 ≤ CFSG.Open.twoRank G →
      ¬ TwoSubgroupsFourGenerated G →
      DConnected (CoreAssembly.conjClass (satU (.sl2 3 1) K z)) →
      BootData3 (conjClass3 (satU (.sl2 3 1) K z)) →
      ¬ IndepTriple3 (conjClass3 (satU (.sl2 3 1) K z)) →
      Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥


theorem oddCentralizerFree_of_exact_sat {G : Type} [Group G] [Finite G] {K : Subgroup G} {z : G}
    (hz : IsClassicalMemberU (.sl2 3 1) K z)
    (hex : ExactMembers3 (conjClass3 (satU (.sl2 3 1) K z))) :
    Balance.oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥ :=
  oddCentralizerFree_of_exact_intrinsic ((hz.satU_member).toQ3 (by norm_num))
    (oddCoreIn_le_satU (MemberType.isSolvableType_sl2.mpr (by norm_num)))
    (hex _ ⟨1, conjSub_one _⟩)


end CFSG.ClassicalInvolution.Q3.Q3DB
