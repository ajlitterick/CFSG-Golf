module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TRBridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin

open scoped commutatorElement Pointwise
open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

variable {G : Type} [Group G] [Finite G]

theorem false_of_both_le_gnC {M X₀ T L₁ L₂ : Subgroup G} (hTX : T ≤ X₀)
    (hT2 : IsPGroup 2 T) (hT0 : T ≠ ⊥) (hD : GNBound (T.subgroupOf X₀))
    (hL₁X : L₁ ≤ X₀) (hL₁M : L₁ ≤ M) (hL₂M : L₂ ≤ M)
    (hp₁ : ⁅L₁, L₁⁆ = L₁)
    (hc : ⁅barM M L₁, barM M L₂⁆ = ⊥)
    (hZ₁ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barM M L₁)))
    (h3₁ : 3 ∣ Nat.card (barM M L₁)) (h3₂ : 3 ∣ Nat.card (barM M L₂))
    (hL₂X : L₂ ≤ X₀)
    (hle₁ : L₁.subgroupOf X₀ ≤ gnC (T.subgroupOf X₀))
    (hle₂ : L₂.subgroupOf X₀ ≤ gnC (T.subgroupOf X₀)) : False := by
  have hTh2 : IsPGroup 2 ↥(T.subgroupOf X₀) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTX).symm
  have hTh0 : T.subgroupOf X₀ ≠ ⊥ := by
    intro h
    apply hT0
    have := Subgroup.map_subgroupOf_eq_of_le hTX
    rw [h, Subgroup.map_bot] at this
    exact this.symm
  set Z : Subgroup ↥X₀ := Quasithin.omegaOneCenterOf (T.subgroupOf X₀) with hZ
  have hZb : Z ≠ ⊥ := QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hTh2 hTh0
  have hZT : Z ≤ T.subgroupOf X₀ := QuasithinUnique.Setup.omegaOneCenterOf_le _
  have hZc : (Z.subgroupOf (T.subgroupOf X₀)).Characteristic :=
    QuasithinUnique.Setup.characteristic_omegaOneCenterOf _
  obtain ⟨hr, hp⟩ := hD Z hZb hZT hZc
  have hnorm : ∀ l ∈ gnC (T.subgroupOf X₀), l ∈ Subgroup.normalizer (Z : Set ↥X₀) := by
    intro l hl
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzV : z ∈ gnV (T.subgroupOf X₀) := Subgroup.subset_normalClosure hz
    exact Subgroup.mem_centralizer_iff.mp hl z hzV
  have hsup : L₁.subgroupOf X₀ ⊔ L₂.subgroupOf X₀ ≤ Subgroup.normalizer (Z : Set ↥X₀) :=
    sup_le (fun l hl => hnorm l (hle₁ hl)) (fun l hl => hnorm l (hle₂ hl))
  have hc' : ∀ a ∈ barM M L₁, ∀ b ∈ barM M L₂, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp
      ((Subgroup.commutator_eq_bot_iff_le_centralizer).mp hc ha) b hb).symm
  have hi : Nat.Coprime 3 (Nat.card (barM M L₁ ⊓ barM M L₂ : Subgroup _)) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro hdvd
    apply hZ₁
    rw [← card_inf_centralizer_eq_card_center]
    refine hdvd.trans (Subgroup.card_dvd_of_le fun u hu => ⟨hu.1, ?_⟩)
    exact Subgroup.mem_centralizer_iff.mpr fun g hg => hc' g hg u hu.2
  have hrk : 2 ≤ Open.pRank 3 (Subgroup.normalizer (Z : Set ↥X₀)) := by
    have h1 := pRank_add_le_pRank_sup_of_coprime Nat.prime_three hc' hi
    have h2 := CFSG.AGLEmbeddingD2.one_le_pRank_of_dvd Nat.prime_three h3₁
    have h3 := CFSG.AGLEmbeddingD2.one_le_pRank_of_dvd Nat.prime_three h3₂
    have h4 : Open.pRank 3 (barM M L₁ ⊔ barM M L₂) =
        Open.pRank 3 (L₁.subgroupOf X₀ ⊔ L₂.subgroupOf X₀) := by
      rw [← barM_sup_eq hL₁M hL₂M, pRank_barM_eq Nat.prime_three (by norm_num) M _ (sup_le hL₁M hL₂M),
        ← CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective 3 Nat.prime_three X₀.subtype
          X₀.subtype_injective, Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hL₁X,
        Subgroup.map_subgroupOf_eq_of_le hL₂X]
    have h5 := CFSG.PreuniquenessRankFour.Helpers.pRank_mono 3 Nat.prime_three hsup
    have h6 : Open.pRank 3 (barM M L₁) = Open.pRank 3 L₁ :=
      pRank_barM_eq Nat.prime_three (by norm_num) M L₁ hL₁M
    omega
  have h3L₁ : 3 ∣ Nat.card L₁ := by
    refine h3₁.trans ?_
    unfold barM
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₁M).toEquiv]
    exact Subgroup.card_map_dvd _ _
  have h3L₁' : 3 ∣ Nat.card (L₁.subgroupOf X₀) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₁X).toEquiv]
    exact h3L₁
  exact hp hrk _ (fun l hl => hsup (Subgroup.mem_sup_left hl)) (perfect_subgroupOf hL₁X hp₁) h3L₁'


end CFSG.AGLEmbeddingD2.McLaughlin
