module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.AGL81I811Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ThreeComponentCyclic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.TwoLocalN1
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.CyclicSylowNormal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.TwoLocalSylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.PushUpInput

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbeddingD2 CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs CFSG.AGLEmbedding CFSG.AGLEmbeddingD2.Tits.MsidePrelim


theorem eq_of_card_three_of_le_normalizer {G : Type} [Group G] [Finite G] {B A A' : Subgroup G}
    (hcyc : ∀ X : Subgroup G, X ≤ B → IsPGroup 3 X → IsCyclic X) (hAB : A ≤ B) (hA'B : A' ≤ B)
    (hA : Nat.card A = 3) (hA' : Nat.card A' = 3) (hn : A' ≤ Subgroup.normalizer (A : Set G)) :
    A' = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by rw [hA, pow_one])
  have hA'p : IsPGroup 3 A' := IsPGroup.of_card (n := 1) (by rw [hA', pow_one])
  have hQ : IsPGroup 3 (A ⊔ A' : Subgroup G) := hAp.to_sup_of_normal_left' hA'p hn
  haveI : IsCyclic ↥(A ⊔ A' : Subgroup G) := hcyc _ (sup_le hAB hA'B) hQ
  have hAle : A ≤ A ⊔ A' := le_sup_left
  have hA'le : A' ≤ A ⊔ A' := le_sup_right
  have h1 : A'.subgroupOf (A ⊔ A') = A.subgroupOf (A ⊔ A') := by
    apply eq_of_card_eq_of_isCyclic
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAle).toEquiv, hA, hA']
  have h2 := Subgroup.subgroupOf_inj.mp h1
  rwa [inf_of_le_left hA'le, inf_of_le_left hAle] at h2


end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
