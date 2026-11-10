module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbedding.BlockFactsThreeFive
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeAbstract
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp48Rank7Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding
open CFSG.AGLEmbedding.ParabPrime
open scoped commutatorElement


variable {G : Type} [Group G] [Finite G]

@[expose] def D1CaseTwoAlphaR (p : ℕ) (M H R : Subgroup G) : Prop :=
  ∃ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L ∧ (L.subgroupOf M).Normal ∧
    p ∣ Nat.card (perfectJoin (blockPL M (pCoreOf 2 H) L)) ∧
    ∃ a : ↥M, (a : G) ∈ R ∧
      ¬ ∃ v ∈ perfectJoin (blockPL M (pCoreOf 2 H) L),
        ∀ w ∈ perfectJoin (blockPL M (pCoreOf 2 H) L),
          ⁅QuotientGroup.mk' (CFSG.pCore 2 ↥M) a * v, w⁆ ∈
            pCoreOf 2 (perfectJoin (blockPL M (pCoreOf 2 H) L))

end CFSG.LocalAnalysis.RankThreeTheoremC
