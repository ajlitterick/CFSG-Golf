module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.LowRankRow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.OneImageCensus

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.Open CFSG.QuasithinUnique

@[expose] def KFactNineThreeThreeTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), Open.IsKGroup ↥M →
    Asc81bHyp M S → IsWeakSBlock M S L → ¬ InClassXBlock L → ¬ IsSylowTwoOf (S ⊓ L) L →
    NineThreeThree M S L → 2 ≤ Open.pRank 3 L →
    ¬ Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 6)) → ¬ BlockPLThreeSolv M S L

@[expose] def KFactNineThreeThreeFive : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M S L : Subgroup G), IsWeakSBlock M S L →
    NineThreeThree M S L → Nonempty (↥(barM M L) ≃* alternatingGroup (Fin 5)) → NineThreeOne L

variable {G : Type} [Group G] [Finite G]

theorem kFactNineThreeThreeBig_of_two (h : KFactNineThreeThreeTwo) : KFactNineThreeThreeBig := by
  intro G _ _ M S L hK hA hL hX hS h3 hr hsolv
  refine h G M S L hK hA hL hX hS h3 (by omega) ?_ hsolv
  rintro ⟨e⟩
  have hrb : Open.pRank 3 (⊤ : Subgroup ↥(barM M L)) = Open.pRank 3 L := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, pRank_barM_eq Nat.prime_three
      (by norm_num) M L hL.le]
  have hrk := (CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.prime_three.one_lt e).symm.trans hrb
  have := pRank_three_alternating_le (N := 6)
  omega


end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
