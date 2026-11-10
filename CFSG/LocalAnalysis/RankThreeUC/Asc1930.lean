module

public import CFSG.LocalAnalysis.RankThreeUC.Assembly
public import CFSG.LocalAnalysis.RankThreeUC.ClauseCTI
public import CFSG.Quasithin.Background.E1Sections

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Quasithin.E1 (IsCompositionFactor)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

section Lists

variable {G : Type} [Group G]

@[expose] def Asc1930ListA (L : Type) [Group L] : Prop :=
  ∃ n : ℕ, Odd n ∧ 1 < n ∧
    (LieModel L .PSL 2 2 n ∨ LieModel L .PSL 3 2 n ∨ LieModel L .twistedB2 0 2 n)

@[expose] def Asc1930ListB (L : Type) [Group L] : Prop :=
  (∃ (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m n : ℕ), 2 < n ∧ LieModel L t m 2 n) ∨
    LieModel L .trialityD4 0 2 1 ∨ LieModel L .trialityD4 0 2 2 ∨
    LieModel L .PSU 4 2 2 ∨ LieModel L .PSU 5 2 2 ∨ LieModel L .POmegaMinus 4 2 2 ∨
    Nonempty (L ≃* alternatingGroup (Fin 9))

theorem listA_le_listB (L : Type) [Group L] (h : Asc1930ListA L) : Asc1930ListB L := by
  obtain ⟨n, ⟨k, rfl⟩, hn, h | h | h⟩ := h
  · exact Or.inl ⟨.PSL, 2, 2 * k + 1, by omega, h⟩
  · exact Or.inl ⟨.PSL, 3, 2 * k + 1, by omega, h⟩
  · exact Or.inl ⟨.twistedB2, 0, 2 * k + 1, by omega, h⟩

@[expose] def Asc1930HasA (H : Subgroup G) : Prop :=
  ∃ (L : Type) (_ : Group L), IsCompositionFactor ↥H L ∧ Asc1930ListA L

@[expose] def Asc1930HasB (H : Subgroup G) : Prop :=
  ∃ (L : Type) (_ : Group L), IsCompositionFactor ↥H L ∧ Asc1930ListB L

@[expose] def Asc1930 (M H : Subgroup G) : Prop :=
  Asc1930HasB H ∧ (IsStronglyPEmbedded 3 M → Asc1930HasA H)

@[expose] def Hyp124 (M H : Subgroup G) : Prop :=
  ¬ Asc1930HasA H ∧ (¬ IsStronglyPEmbedded 3 M → ¬ Asc1930HasB H)

theorem asc1930_iff_not_hyp124 (M H : Subgroup G) : Asc1930 M H ↔ ¬ Hyp124 M H := by
  classical
  unfold Asc1930 Hyp124
  constructor
  · rintro ⟨hB, hA⟩ ⟨hnA, hnB⟩
    by_cases hs : IsStronglyPEmbedded 3 M
    · exact hnA (hA hs)
    · exact hnB hs hB
  · intro h
    by_cases hA : Asc1930HasA H
    · obtain ⟨L, _, hL, hLA⟩ := hA
      exact ⟨⟨L, inferInstance, hL, listA_le_listB L hLA⟩, fun _ => ⟨L, inferInstance, hL, hLA⟩⟩
    · by_cases hs : IsStronglyPEmbedded 3 M
      · exact absurd ⟨hA, fun hn => absurd hs hn⟩ h
      · by_cases hB : Asc1930HasB H
        · exact ⟨hB, fun hs' => absurd hs' hs⟩
        · exact absurd ⟨hA, fun _ => hB⟩ h

end Lists

section MSigma

variable {G : Type} [Group G] [Finite G]

@[expose] def SigmaTwo (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  p ∈ rankThreeSigmaA G ∧
    ∃ (P : Sylow p G) (M : Subgroup G), IsWitness p P M ∧ rankThreeClauseB M (P : Subgroup G) p

@[expose] def SigmaChoice (G : Type) [Group G] [Finite G] (p : ℕ) : Prop :=
  (3 ∈ rankThreeSigmaA G → p = 3) ∧
    (3 ∉ rankThreeSigmaA G → (∃ q, SigmaTwo G q) → SigmaTwo G p)

@[expose] def Setup.InMSigma (S : Setup G) : Prop :=
  SigmaChoice G S.p

theorem exists_sigmaChoice (hS : Standing G) : ∃ p ∈ rankThreeSigmaA G, SigmaChoice G p := by
  by_cases h3 : 3 ∈ rankThreeSigmaA G
  · exact ⟨3, h3, fun _ => rfl, fun h => absurd h3 h⟩
  by_cases hq : ∃ q, SigmaTwo G q
  · obtain ⟨q, hq'⟩ := hq
    exact ⟨q, hq'.1, fun h => absurd h h3, fun _ _ => hq'⟩
  · obtain ⟨p, hp⟩ :=
      CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_nonempty_of_evenRank_three hS.rank
    exact ⟨p, hp, fun h => absurd h h3, fun _ h => absurd h hq⟩

end MSigma

section Stages

variable {G : Type} [Group G] [Finite G]

@[expose] def SmallNH1930 (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ S : Setup G, S.InMSigma → ∀ H ∈ hSet S.T S.M, Asc1930 S.M H

@[expose] def NotTIStage1930 (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ S : Setup G, S.InMSigma → (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
    CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T)


@[expose] def TIStage1930 (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ S : Setup G, S.InMSigma → (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) →
    CFSG.CGT.Timmesfeld75.IsTI (uCore S.M S.T) → False

@[expose] def LargeNH1930 (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ S : Setup G, S.InMSigma → (∀ H ∈ hSet S.T S.M, Asc1930 S.M H) → False

@[expose] def UniquenessStageB1930 (G : Type) [Group G] [Finite G] : Prop :=
  rankThreeUC G → ∀ S : Setup G, S.InMSigma → False


theorem largeNH1930_of_stages (h1 : NotTIStage1930 G) (h2 : TIStage1930 G) : LargeNH1930 G :=
  fun hUC S hMS hsmall => h2 hUC S hMS hsmall (h1 hUC S hMS hsmall)

theorem uniquenessStageB_of_small_large1930 (h1 : SmallNH1930 G) (h2 : LargeNH1930 G) :
    UniquenessStageB1930 G :=
  fun hUC S hMS => h2 hUC S hMS (h1 hUC S hMS)


end Stages

end CFSG.LocalAnalysis.RankThreeUC
