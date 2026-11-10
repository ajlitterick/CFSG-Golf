module

public import CFSG.ClassicalInvolution.SmallCases.FrameRank
public import CFSG.ClassicalInvolution.PerfectCase

public section

namespace CFSG.ClassicalInvolution

open CFSG.Open CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

section Configuration

variable {G : Type*} [Group G]

@[expose] def A2Configuration (z : G) (J : Subgroup G) : Prop :=
  ∃ g h : G, J.map (MulAut.conj g⁻¹).toMonoidHom ≠ J.map (MulAut.conj h⁻¹).toMonoidHom ∧
    g⁻¹ * z * g ≠ h⁻¹ * z * h ∧
    (g⁻¹ * z * g) * (h⁻¹ * z * h) = (h⁻¹ * z * h) * (g⁻¹ * z * g) ∧
    ¬ Commutes (J.map (MulAut.conj g⁻¹).toMonoidHom) (J.map (MulAut.conj h⁻¹).toMonoidHom)


end Configuration

section PartOne


end PartOne

section Simple

@[expose] def SL2Witness {G : Type*} [Group G] (J : Subgroup G) : Prop :=
  ∃ p n : ℕ, ∃ _ : Fact p.Prime, p ≠ 2 ∧ 0 < n ∧
    Nonempty (J ⧸ classicalInvolutionOddCore J ≃* SL(2, GaloisField p n))

@[expose] def A7Witness {G : Type*} [Group G] (J : Subgroup G) : Prop :=
  CFSG.Open.IsQuasisimple (J ⧸ classicalInvolutionOddCore J) ∧
    Nat.card (Subgroup.center (J ⧸ classicalInvolutionOddCore J)) = 2 ∧
    Nonempty ((J ⧸ classicalInvolutionOddCore J) ⧸
      Subgroup.center (J ⧸ classicalInvolutionOddCore J) ≃* alternatingGroup (Fin 7))

theorem classicalInvolutionWitness_iff {G : Type*} [Group G] (J : Subgroup G) :
    classicalInvolutionWitness J ↔ SL2Witness J ∨ A7Witness J :=
  Iff.rfl

@[expose] def TwoSubgroupsFourGenerated (F : Type*) [Group F] : Prop :=
  ∀ P : Subgroup F, IsPGroup 2 P → ∃ s : Finset F, s.card ≤ 4 ∧ Subgroup.closure (s : Set F) = P

@[expose] def CITSimplePerfectUnder
    (P : ∀ {F : Type} [Group F] [Finite F], F → Subgroup F → Prop) : Prop :=
  ∀ (F : Type) [Group F] [Finite F] [IsSimpleGroup F], (∃ a b : F, a * b ≠ b * a) →
    ∀ z : F, orderOf z = 2 → ∀ K : Subgroup F, z ∈ K →
    IsSubnormal K (Subgroup.centralizer ({z} : Set F)) → classicalInvolutionWitness K →
    ¬ Group.IsSolvable K → P z K →
    Blueprint.OddLieType F ∨ Blueprint.NativeSporadic.IsSporadic F .M11

@[expose] def SmallConfiguration (F : Type) [Group F] [Finite F] (K : Subgroup F) : Prop :=
  3 ≤ twoRank F ∧ ¬ TwoSubgroupsFourGenerated F ∧ ¬ HasEFrameRank4 K

abbrev CITFrameRankFour : Prop :=
  CITSimplePerfectUnder fun _ K => HasEFrameRank4 K

abbrev CITRankTwo : Prop :=
  CITSimplePerfectUnder fun {F} _ _ _ _ => twoRank F ≤ 2

abbrev CITSectionalFour : Prop :=
  CITSimplePerfectUnder fun {F} _ _ _ _ => 3 ≤ twoRank F ∧ TwoSubgroupsFourGenerated F

abbrev CIT2A7 : Prop :=
  CITSimplePerfectUnder fun {F} _ _ _ K => SmallConfiguration F K ∧ A7Witness K

abbrev CITDisconnected : Prop :=
  CITSimplePerfectUnder fun {F} _ _ _ K =>
    SmallConfiguration F K ∧ SL2Witness K ∧ ¬ DeltaConnected K

abbrev CITConnectedA2 : Prop :=
  CITSimplePerfectUnder fun {F} _ _ z K =>
    SmallConfiguration F K ∧ SL2Witness K ∧ DeltaConnected K ∧ A2Configuration z K

abbrev CITTypeC : Prop :=
  CITSimplePerfectUnder fun {F} _ _ z K =>
    SmallConfiguration F K ∧ SL2Witness K ∧ DeltaConnected K ∧ ¬ A2Configuration z K

theorem citSimplePerfect_of_cases (hF : CITFrameRankFour) (h0 : CITRankTwo)
    (h1 : CITSectionalFour) (h2 : CIT2A7) (h3 : CITDisconnected) (h4 : CITConnectedA2)
    (h5 : CITTypeC) : CITSimplePerfect := by
  intro F _ _ _ hnab z hz K hzK hK hw hns
  by_cases hf : HasEFrameRank4 K
  · exact hF F hnab z hz K hzK hK hw hns hf
  by_cases hr : twoRank F ≤ 2
  · exact h0 F hnab z hz K hzK hK hw hns hr
  by_cases hs : TwoSubgroupsFourGenerated F
  · exact h1 F hnab z hz K hzK hK hw hns ⟨by omega, hs⟩
  have hsmall : SmallConfiguration F K := ⟨by omega, hs, hf⟩
  rcases (classicalInvolutionWitness_iff K).mp hw with hsl | ha7
  · by_cases hc : DeltaConnected K
    · by_cases ha : A2Configuration z K
      · exact h4 F hnab z hz K hzK hK hw hns ⟨hsmall, hsl, hc, ha⟩
      · exact h5 F hnab z hz K hzK hK hw hns ⟨hsmall, hsl, hc, ha⟩
    · exact h3 F hnab z hz K hzK hK hw hns ⟨hsmall, hsl, hc⟩
  · exact h2 F hnab z hz K hzK hK hw hns ⟨hsmall, ha7⟩


end Simple

end CFSG.ClassicalInvolution
