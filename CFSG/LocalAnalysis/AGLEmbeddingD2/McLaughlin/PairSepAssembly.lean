module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairFacts
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.WeakBlockDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers


@[expose] def PairBlockCentreThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P : Sylow 3 G) (M A H R : Subgroup G),
    PairStrongCtx P M A H R → ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L →
    3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _) →
    ∃ y ∈ barM M (Subgroup.normalizer (pCoreOf 2 H : Set G) ⊓ L), y ^ 3 = 1 ∧
      y ∉ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M))

end CFSG.AGLEmbeddingD2.McLaughlin
