module

public import CFSG.ClassicalInvolution.Balance.LayerGenerationField
import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.ClassicalInvolution.Balance.PassTwoModelFacts
public import CFSG.ClassicalInvolution.Balance.PassTwoP1

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank

section Definitions

variable {G : Type} [Group G]

@[expose] def IsFaithfulFourGroupAt (E : Subgroup G) (a : G) (L : Subgroup (OddQuot a))
    (F₀ : Subgroup G) : Prop :=
  F₀ ≤ E ∧ Nat.card F₀ = 4 ∧ modOdd a F₀ ≤ Subgroup.normalizer (L : Set (OddQuot a)) ∧
    ∀ f ∈ modOdd a F₀, f ≠ 1 → ¬ ∀ x ∈ L, f * x = x * f

@[expose] def LayerGenerationOn (Ω : Set (Subgroup G)) (E : Subgroup G) (a : G)
    (P : Subgroup (OddQuot a) → Prop) : Prop :=
  ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L → P L → L ≤ memberJoin Ω a →
    ∀ F₀ : Subgroup G, IsFaithfulFourGroupAt E a L F₀ → OddCentralizerFree (modOdd a F₀) L

@[expose] def LayerGenerationLie (Ω : Set (Subgroup G)) (E : Subgroup G) (a : G) : Prop :=
  LayerGenerationOn Ω E a fun L => IsOddLieComponent L

@[expose] def LayerGenerationLieBig (Ω : Set (Subgroup G)) (E : Subgroup G) (a : G) : Prop :=
  LayerGenerationOn Ω E a fun L => IsOddLieComponentBig L

theorem LayerGenerationLie.toBig {Ω : Set (Subgroup G)} {E : Subgroup G} {a : G}
    (h : LayerGenerationLie Ω E a) : LayerGenerationLieBig Ω E a :=
  fun L hL hbig hjoin => h L hL hbig.isOddLieComponent hjoin


end Definitions

section Providers

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {E : Subgroup G}

omit [Finite G] in
theorem modOdd_sq_eq_one {a : G} {F₀ : Subgroup G} (hE2 : ∀ x ∈ E, x * x = 1) (hF₀E : F₀ ≤ E) :
    ∀ f ∈ modOdd a F₀, f * f = 1 := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' : (x : G) ∈ F₀ := hx
  rw [← map_mul]
  have : x * x = 1 := Subtype.ext (hE2 _ (hF₀E hx'))
  rw [this, map_one]

theorem IsFaithfulFourGroupAt.oddCentralizerFree_of_model (hE2 : ∀ x ∈ E, x * x = 1)
    (hmodel : LayerGenerationModel) {a : G} (ha : a ∈ E) {L : Subgroup (OddQuot a)}
    (hL : CFSG.IsComponent L) (hbig : IsOddLieComponentBig L) {F₀ : Subgroup G}
    (hF : IsFaithfulFourGroupAt E a L F₀) : OddCentralizerFree (modOdd a F₀) L := by
  obtain ⟨hF₀E, h4, hFn, hfaith⟩ := hF
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (comm_of_sq_eq_one hE2 ha (hF₀E hf)).symm
  have hF2 : ∀ f ∈ F₀, f * f = 1 := fun f hf => hE2 f (hF₀E hf)
  exact OddCentralizerFree.of_le_layers
    (hmodel (OddQuot a) L hL hbig (modOdd a F₀)
      (by rw [card_modOdd_of_exponent_two hFC hF2, h4]) (modOdd_sq_eq_one hE2 hF₀E) hFn hfaith)

theorem IsFaithfulFourGroupAt.oddCentralizerFree_of_centralizedGenerated
    (hE2 : ∀ x ∈ E, x * x = 1) {𝒜 : Set (Subgroup G)} (h𝒜 : ∀ K ∈ 𝒜, IsInvolutionMember K) {a : G}
    {L : Subgroup (OddQuot a)} (hL : CFSG.IsComponent L) (hlie : IsOddLieComponent L)
    {F₀ : Subgroup G} (hF : IsFaithfulFourGroupAt E a L F₀)
    (hgen : CentralizedGeneratedAt 𝒜 a F₀ L) : OddCentralizerFree (modOdd a F₀) L := by
  obtain ⟨hF₀E, h4, hFn, hfaith⟩ := hF
  have hB := involutionCentralizerB_of_isOddLieComponent
    ((CFSG.isComponent_iff_open L).mp hL).2.2 hlie
  exact OddCentralizerFree.of_members l2PrimeBalance hL
    (fun f hf hf1 => hB f hf1 (modOdd_sq_eq_one hE2 hF₀E f hf) (hFn hf))
    (hgen.oddCentralizerFreeMembers h𝒜)

end Providers

section FrameProviders

variable {F : Type*} [Field F] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G} {S : Set (Subgroup G)}


theorem LayerGenerationLieBig.of_model (hE2 : ∀ x ∈ E, x * x = 1) (hmodel : LayerGenerationModel)
    {a : G} (ha : a ∈ E) : LayerGenerationLieBig Ω E a :=
  fun _ hL hbig _ _ hF => hF.oddCentralizerFree_of_model hE2 hmodel ha hL hbig


end FrameProviders

section Chain

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {E : Subgroup G}

omit [Finite G] in
theorem componentLayersAt_of_layerGenerationOn {a : G} {P : Subgroup (OddQuot a) → Prop}
    (htri : ∀ L : Subgroup (OddQuot a), CFSG.IsComponent L →
      OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨ (P L ∧ L ≤ memberJoin Ω a))
    (hlay : LayerGenerationOn Ω E a P) : ComponentLayersAt Ω E a := by
  intro L hL
  rcases htri L hL with h | h | ⟨hP, hjoin⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr fun F₀ hF₀E h4 hFn hfaith =>
      hlay L hL hP hjoin F₀ ⟨hF₀E, h4, hFn, hfaith⟩)


end Chain

end CFSG.ClassicalInvolution.Balance
