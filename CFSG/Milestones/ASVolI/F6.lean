module

public import CFSG.Milestones.ASVolI.A2
public import CFSG.Quasithin.Background.RonanF615QTK
public import CFSG.Quasithin.Background.RonanF617

public section

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F6

structure HypF_6_2 {D : Type} [Group D] (G₁ G₂ D₁ D₂ : Subgroup D) : Prop where
  triple : IsGoldschmidtTriple G₁ G₂
  sylow₁ : D₁ ≤ G₁ ∧ IsPGroup 3 D₁ ∧ ¬ 3 ∣ D₁.relIndex G₁
  sylow₂ : D₂ ≤ G₂ ∧ IsPGroup 3 D₂ ∧ ¬ 3 ∣ D₂.relIndex G₂

@[expose] def IsQuotientOfSQTK (X : Type) [Group X] : Prop :=
  ∃ (E : Type) (_ : Group E) (_ : Finite E) (M : Subgroup E) (_ : M.Normal),
    CFSG.SectionRank.IsSQTKCat E ∧ Nonempty (X ≃* E ⧸ M)

@[expose] def IsQuotientOfQTK (X : Type) [Group X] : Prop :=
  ∃ (E : Type) (_ : Group E) (_ : Finite E) (M : Subgroup E) (_ : M.Normal),
    IsQuasithin E ∧ CFSG.SectionRank.IsKGroupCat E ∧ Nonempty (X ≃* E ⧸ M)

@[expose] def IsSQTKModOThreePrime (X : Type) [Group X] : Prop :=
  ∃ (E : Type) (_ : Group E) (_ : Finite E),
    CFSG.SectionRank.IsSQTKCat E ∧ Nonempty (X ≃* E ⧸ CFSG.pPrimeCore 3 E)

@[expose] def IsQTKModOThreePrime (X : Type) [Group X] : Prop :=
  ∃ (E : Type) (_ : Group E) (_ : Finite E),
    IsQuasithin E ∧ CFSG.SectionRank.IsKGroupCat E ∧ Nonempty (X ≃* E ⧸ CFSG.pPrimeCore 3 E)

structure HypF_1_1_abcd {G : Type} [Group G] (Li Lj S : Subgroup G) : Prop where
  finite : Finite ↥S
  pgroup : IsPGroup 2 S
  normalizes : S ≤ Subgroup.normalizer (Li : Set G)
  sylow : IsSylowTwoOf (S ⊓ Li) Li
  listed : IsRankOneListed (oTwoQuot ↥Li)
  borel_le : borelOf Lj S ≤ Subgroup.normalizer (Li : Set G)

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F6
open CFSG.ASVolI.ChF

@[expose] def F_6_3 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    IsGreatest {N : Subgroup D | N ≤ G₁ ⊓ G₂ ∧ (N.subgroupOf G₁).Normal ∧ (N.subgroupOf G₂).Normal}
      (CFSG.pCore 2 D)


@[expose] def F_6_5 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    ∀ H₁ H₂ : Subgroup (D ⧸ CFSG.pCore 2 D),
      H₁ = G₁.map (QuotientGroup.mk' (CFSG.pCore 2 D)) →
      H₂ = G₂.map (QuotientGroup.mk' (CFSG.pCore 2 D)) →
      IsGoldschmidtAmalgam H₁ H₂ ∧
      IsGoldCaseCat H₁ H₂ ∧
      ((IsGoldCaseVICat H₁ H₂ ∨ IsGoldCaseVICat H₂ H₁) →
        CharTwo H₁ ∧ CharTwo H₂ ∧ IsWeakBNPair H₁ H₂) ∧
      ((IsGoldCaseI H₁ H₂ ∨ IsGoldCaseII H₁ H₂ ∨ IsGoldCaseIII H₁ H₂ ∨ IsGoldCaseIV H₁ H₂ ∨
          IsGoldCaseV H₁ H₂ ∨ IsGoldCaseI H₂ H₁ ∨ IsGoldCaseII H₂ H₁ ∨ IsGoldCaseIII H₂ H₁ ∨
          IsGoldCaseIV H₂ H₁ ∨ IsGoldCaseV H₂ H₁) →
        ¬ IsPGroup 2 ↥(CFSG.generalizedFitting ↥H₁) ∨ ¬ IsPGroup 2 ↥(CFSG.generalizedFitting ↥H₂))

section F65Cert


end F65Cert

@[expose] def F_6_6 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    twoResidual (⊤ : Subgroup D) = twoResidual G₁ ⊔ twoResidual G₂


@[expose] def F_6_7 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    ∀ X : Subgroup D, X.IsSubnormal →
      List.TFAE [G₁ ⊓ X ≤ pCoreOf 2 G₁,
        G₁ ⊓ X = pCoreOf 2 G₁ ⊓ X ∧ pCoreOf 2 G₁ ⊓ X = G₁ ⊓ G₂ ⊓ X ∧
          IsSylowTwoOf (G₁ ⊓ G₂ ⊓ X) X,
        ¬ twoResidual G₁ ≤ X] ∧
      List.TFAE [G₂ ⊓ X ≤ pCoreOf 2 G₂,
        G₂ ⊓ X = pCoreOf 2 G₂ ⊓ X ∧ pCoreOf 2 G₂ ⊓ X = G₁ ⊓ G₂ ⊓ X ∧
          IsSylowTwoOf (G₁ ⊓ G₂ ⊓ X) X,
        ¬ twoResidual G₂ ≤ X]


@[expose] def F_6_8 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    ∀ X : Subgroup D, X.Normal → G₁ ⊓ X ≤ pCoreOf 2 G₁ → G₂ ⊓ X ≤ pCoreOf 2 G₂ →
      G₁ ⊓ G₂ ⊓ X ≤ CFSG.pCore 2 D ∧
      Odd (Nat.card ↥(X.map (QuotientGroup.mk' (CFSG.pCore 2 D)))) ∧
      Group.IsSolvable ↥(X.map (QuotientGroup.mk' (CFSG.pCore 2 D)))


@[expose] def F_6_9 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    Group.IsSolvable D → IsQuotientOfSQTK D →
    (twoResidual G₁ ≤ Subgroup.centralizer (opResidual 3 (CFSG.fittingSubgroup D) : Set D) ∨
      twoResidual G₂ ≤ Subgroup.centralizer (opResidual 3 (CFSG.fittingSubgroup D) : Set D)) →
    ∀ q : ℕ, q.Prime → q ∣ Nat.card D → q = 2 ∨ q = 3


@[expose] def F_6_10 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    ¬ Group.IsSolvable D → IsQuotientOfQTK D →
    ∀ K : Subgroup D, CFSG.IsComponent K →
      ((twoResidual G₁ ≤ K ∧ K ⊔ G₂ = ⊤) ∨ (twoResidual G₂ ≤ K ∧ K ⊔ G₁ = ⊤)) ∧ K.Normal ∧
      ¬ K ≤ CFSG.pPrimeCore 3 D

section F610Cert


end F610Cert

@[expose] def F_6_11 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    (IsSylowTwoOf (CFSG.pCore 2 D) (CFSG.pPrimeCore 3 D) ∧
      Group.IsSolvable ↥(CFSG.pPrimeCore 3 D)) ∧
    ∀ (H₁ H₂ : Subgroup (D ⧸ CFSG.pCore 2 D)) (G₁' G₂' : Subgroup (D ⧸ CFSG.pPrimeCore 3 D)),
      H₁ = G₁.map (QuotientGroup.mk' (CFSG.pCore 2 D)) →
      H₂ = G₂.map (QuotientGroup.mk' (CFSG.pCore 2 D)) →
      G₁' = G₁.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 D)) →
      G₂' = G₂.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 D)) →
        ((G₁' ⊓ G₂' = (G₁ ⊓ G₂).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 D)) ∧
            IsGoldschmidtAmalgam G₁' G₂' ∧ IsAmalgamIso G₁' G₂' H₁ H₂) ∨
          (pCoreOf 2 G₁ = CFSG.pCore 2 D ∧ pCoreOf 2 G₂ = CFSG.pCore 2 D ∧
            Nonempty ((D ⧸ CFSG.pPrimeCore 3 D) ≃* Equiv.Perm (Fin 3)) ∧
            G₁ ⊔ CFSG.pPrimeCore 3 D = ⊤ ∧
            ¬ ∃ x ∈ CFSG.pPrimeCore 3 D, CFSG.pPrimeCore 3 D ≤ Subgroup.zpowers x ⊔ CFSG.pCore 2 D))


@[expose] def F_6_12 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    CFSG.pCore 2 D = ⊥ →
    ((∀ S : Subgroup D, S ≤ pCoreOf 2 G₁ → S ≠ ⊥ → D₁ ≤ Subgroup.normalizer (S : Set D) →
        ¬ (pCoreOf 2 G₁ ⊔ twoResidual G₂ ≤ Subgroup.normalizer (S : Set D))) ∧
      (∀ S : Subgroup D, S ≤ pCoreOf 2 G₁ → S ≠ ⊥ → (S.subgroupOf (pCoreOf 2 G₁)).Characteristic →
        ¬ (pCoreOf 2 G₁ ⊔ twoResidual G₂ ≤ Subgroup.normalizer (S : Set D)))) ∧
    ((∀ S : Subgroup D, S ≤ pCoreOf 2 G₂ → S ≠ ⊥ → D₂ ≤ Subgroup.normalizer (S : Set D) →
        ¬ (pCoreOf 2 G₂ ⊔ twoResidual G₁ ≤ Subgroup.normalizer (S : Set D))) ∧
      (∀ S : Subgroup D, S ≤ pCoreOf 2 G₂ → S ≠ ⊥ → (S.subgroupOf (pCoreOf 2 G₂)).Characteristic →
        ¬ (pCoreOf 2 G₂ ⊔ twoResidual G₁ ≤ Subgroup.normalizer (S : Set D))))


@[expose] def F_6_13 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    CFSG.pCore 2 D = ⊥ →
    ∀ X : Subgroup D, twoResidual G₁ ≤ X → X.Normal → ¬ twoResidual G₂ ≤ X →
      (X ⊔ G₂ = ⊤ ∧ (X ⊔ pCoreOf 2 G₂).Normal ∧ IsSylowTwoOf (pCoreOf 2 G₂) (X ⊔ pCoreOf 2 G₂)) ∧
      Nonempty (↥(twoResidual G₁) ≃* Multiplicative (ZMod 3)) ∧
      ((IsElemAbelian 2 (pCoreOf 2 G₂) ∧ ∃ n : ℕ, n ≤ 3 ∧ Nat.card ↥(pCoreOf 2 G₂) = 2 ^ n) ∧
        (pCoreOf 2 G₂ ⊔ twoResidual G₁ ≤ Subgroup.normalizer (pCoreOf 2 G₂ : Set D) →
          pCoreOf 2 G₂ = ⊥) ∧
        (pCoreOf 2 G₂ ⊔ twoResidual G₁ ≤
            Subgroup.normalizer (pCoreOf 2 (twoResidual G₂) : Set D) →
          pCoreOf 2 (twoResidual G₂) = ⊥)) ∧
      (oddCoreIn X = X → ⁅pCoreOf 2 G₁, twoResidual G₁⁆ = ⊥)

section F613Cert


end F613Cert

@[expose] def F_6_14 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    twoResidual (⊤ : Subgroup D) = oddCoreIn (⊤ : Subgroup D) → CFSG.pCore 2 D = ⊥ →
      Nonempty (↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2)) ∨
      (Nonempty (↥(pCoreOf 2 G₁) ≃* Multiplicative (ZMod 2)) ∧
        Nonempty (↥(pCoreOf 2 G₂) ≃* Multiplicative (ZMod 2)) ∧
        Nonempty (↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))


@[expose] def F_6_15 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    (IsSQTKModOThreePrime D ∨ IsQTKModOThreePrime D) →
      (CFSG.pPrimeCore 3 D = ⊥ ∧ CFSG.pCore 2 D = ⊥ ∧ IsGoldschmidtAmalgam G₁ G₂ ∧
        IsGoldCaseCat G₁ G₂) ∧
      (IsSQTKModOThreePrime D →
        ∀ K : Subgroup D, CFSG.IsComponent K → CFSG.Milestones.SQTKSimpleList (↥K ⧸ Subgroup.center ↥K)) ∧
      (IsQTKModOThreePrime D →
        ∀ K : Subgroup D, CFSG.IsComponent K → CFSG.ASVolI.ChA.TheoremBList (↥K ⧸ Subgroup.center ↥K))


section F615Full


end F615Full

@[expose] def F_6_16 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    IsSQTKModOThreePrime D → ¬ IsCyclic ↥(CFSG.pCore 3 D) →
      IsPGroup 3 ↥(twoResidual (⊤ : Subgroup D)) ∧
      ((Nonempty (↥(G₁ ⊓ G₂) ≃* Multiplicative (ZMod 2)) ∧ pCoreOf 2 G₁ = ⊥ ∧
          pCoreOf 2 G₂ = ⊥) ∨
        IsF618CaseTwo D)


@[expose] def F_6_17 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    IsQTKModOThreePrime D → IsCyclic ↥(CFSG.pCore 3 D) →
      (twoResidual (⊤ : Subgroup D) = CFSG.generalizedFitting D ∧
        CFSG.IsQuasisimple ↥(twoResidual (⊤ : Subgroup D))) ∨
      (∃ (K Z : Subgroup D) (p e : ℕ),
        IsL2 p e ↥K ∧ (p ^ e % 24 = 11 ∨ p ^ e % 24 = 13) ∧
        Nat.card ↥Z = 3 ∧ K ⊔ Z = twoResidual (⊤ : Subgroup D) ∧ K ⊓ Z = ⊥ ∧
        (∀ k ∈ K, ∀ z ∈ Z, k * z = z * k) ∧
        Nonempty (↥(G₁ ⊓ G₂) ≃* DihedralGroup 4) ∧
        ((Nonempty (↥G₁ ≃* DihedralGroup 12) ∧ Nonempty (↥G₂ ≃* Equiv.Perm (Fin 4))) ∨
          (Nonempty (↥G₂ ≃* DihedralGroup 12) ∧ Nonempty (↥G₁ ≃* Equiv.Perm (Fin 4)))) ∧
        ∀ t ∈ G₁ ⊓ G₂, t ∉ K → InducesOuterAut t K ∧ InducesOuterAut t Z)

section F617Cert


end F617Cert

@[expose] def F_6_4 : Prop :=
  ∀ (D : Type) [Group D] [Finite D] (G₁ G₂ D₁ D₂ : Subgroup D), HypF_6_2 G₁ G₂ D₁ D₂ →
    ∀ H₁ H₂ T' : Subgroup (D ⧸ CFSG.pCore 2 D),
      H₁ = G₁.map (QuotientGroup.mk' (CFSG.pCore 2 D)) →
      H₂ = G₂.map (QuotientGroup.mk' (CFSG.pCore 2 D)) →
      T' = (G₁ ⊓ G₂).map (QuotientGroup.mk' (CFSG.pCore 2 D)) →
      IsGoldschmidtAmalgam H₁ H₂ ∧
      (HypF_1_1_abcd G₁ G₂ (G₁ ⊓ G₂) ∧ HypF_1_1_abcd G₂ G₁ (G₁ ⊓ G₂)) ∧
      (HypF_1_1_abcd H₁ H₂ T' ∧ HypF_1_1_abcd H₂ H₁ T') ∧
      pCoreOf 2 (H₁ ⊔ H₂ ⊔ T') = ⊥ ∧
      ((CharTwo (H₁ ⊔ T' ⊔ borelOf H₂ T') ∧ CharTwo (H₂ ⊔ T' ⊔ borelOf H₁ T')) →
        IsWeakBNPair H₁ H₂ ∧ (IsGoldCaseVICat H₁ H₂ ∨ IsGoldCaseVICat H₂ H₁))


section F64Cert


end F64Cert

end CFSG.ASVolI
