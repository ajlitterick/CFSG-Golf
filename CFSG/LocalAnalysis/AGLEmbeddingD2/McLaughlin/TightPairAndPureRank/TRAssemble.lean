module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRSwap
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRMove
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.OddCentre
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.BlockRows
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRSylow

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

variable {G : Type} [Group G] [Finite G]


@[expose] def L32Atlas : Prop :=
  ∀ (X : Type) [Group X], IsLThreeTwo X → Nat.card X = 168

theorem pRank_top_le_one_of_card_168 {X : Type} [Group X] [Finite X] (h : Nat.card X = 168) :
    Open.pRank 3 (⊤ : Subgroup X) ≤ 1 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨E, -, hE, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 Nat.prime_three
    (⊤ : Subgroup X)
  have h9 : 3 ^ 2 ∣ Nat.card E := by
    rw [hEcard]; exact pow_dvd_pow 3 hlt
  have := h9.trans (Subgroup.card_subgroup_dvd_card E)
  rw [h] at this
  omega

theorem isA6OrU33_of_doubling (hU : U33Atlas) (hL32 : L32Atlas) {M S L : Subgroup G}
    (hw : IsWeakSBlock M S L)
    (hZ : ¬ 3 ∣ Nat.card (barM M L ⊓
      Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) : Subgroup _))
    (hm : 2 ≤ Open.pRank 3 L)
    (hd : IsDoublingList (↥(barM M L) ⧸ Subgroup.center ↥(barM M L))) :
    IsA6OrU33 ↥(barM M L) := by
  have hX : Open.IsQuasisimple ↥(barM M L) := hw.component.2.2
  have hZ' : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L)) := by
    rwa [← card_inf_centralizer_eq_card_center]
  have hodd : Odd (Nat.card (Subgroup.center ↥(barM M L))) := by
    rw [← card_inf_centralizer_eq_card_center]
    exact odd_card_center_barM hw.toIsTwoPrimeComponent
  have hrq := pRank_top_quot_center_eq hw.le hZ
  rcases hd with hL3 | hA6 | hU3
  · exfalso
    have := pRank_top_le_one_of_card_168 (hL32 _ hL3)
    omega
  · have hZb : Subgroup.center ↥(barM M L) = ⊥ := by
      obtain ⟨e⟩ := hA6
      exact tightCentreTrivial_of_atlas hU _ hX (Or.inl ⟨6, Or.inl rfl, ⟨e⟩⟩) hodd hZ'
    obtain ⟨e⟩ := hA6
    obtain ⟨e'⟩ := mulEquiv_of_center_eq_bot hZb e
    exact Or.inl ⟨e'⟩
  · have hZb : Subgroup.center ↥(barM M L) = ⊥ := by
      obtain ⟨d, hd, ⟨e⟩⟩ := hU3
      exact tightCentreTrivial_of_atlas hU _ hX (Or.inr ⟨d, hd, ⟨e⟩⟩) hodd hZ'
    exact Or.inr (IsUThreeThree.of_center_bot hZb hU3)


end CFSG.AGLEmbeddingD2.McLaughlin
