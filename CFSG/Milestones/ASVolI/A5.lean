module

public import CFSG.Milestones.ASVolI.A1
public import CFSG.Quasithin.Background.A1aFStar

public section

namespace CFSG.ASVolI

open CFSG.Open
open CFSG.ASVolI.ChA

namespace ChA

section A5Vocabulary

variable {G : Type} [Group G]

@[expose] def InHT (T H : Subgroup G) : Prop :=
  T ≤ H ∧ pCoreOf 2 H ≠ ⊥

@[expose] def InMT (T M : Subgroup G) : Prop :=
  IsMaxTwoLocalSubgroup M ∧ T ≤ M

@[expose] def VZ (T H : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ h ∈ H, ∃ z ∈ omegaOne 2 (centerOf T), x = h * z * h⁻¹}

@[expose] def OrdLE (T H₁ H₂ : Subgroup G) : Prop :=
  H₁ = (H₁ ⊓ H₂) ⊔ (H₁ ⊓ centralizerOf (VZ T H₁))

@[expose] def InHvT (T H : Subgroup G) : Prop :=
  InHT T H ∧ H = ChA.normalizerOf (VZ T H)

@[expose] def IsUniqueMaxTwoLocalOver (X M : Subgroup G) : Prop :=
  IsMaxTwoLocalSubgroup M ∧ X ≤ M ∧ ∀ M' : Subgroup G, IsMaxTwoLocalSubgroup M' → X ≤ M' → M' = M

end A5Vocabulary

end ChA

@[expose] def A_5_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ → ∀ H : Subgroup G, InHT T H → IsTwoReduced H (VZ T H)

section Bridge

variable {G : Type} [Group G]


end Bridge


@[expose] def A_5_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ →
      (∀ H : Subgroup G, InHT T H → OrdLE T H H) ∧
      (∀ H₁ H₂ : Subgroup G, InHT T H₁ → InHT T H₂ → H₁ ≤ H₂ → OrdLE T H₁ H₂) ∧
      (∀ M : Subgroup G, InMT T M → InHvT T M)


@[expose] def A_5_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ → ∀ H₁ H₂ : Subgroup G, InHT T H₁ → InHT T H₂ →
      OrdLE T H₁ H₂ →
      VZ T H₁ ≤ VZ T H₂ ∧
      H₂ ⊓ centralizerOf (VZ T H₂) ≤ H₂ ⊓ centralizerOf (VZ T H₁) ∧
      (InHvT T H₁ → H₂ ⊓ centralizerOf (VZ T H₂) ≤ H₁ ⊓ centralizerOf (VZ T H₁))


@[expose] def A_5_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ → ∀ H₁ H₂ : Subgroup G, InHvT T H₁ → InHvT T H₂ →
      (H₁ = H₂ ↔ VZ T H₁ = VZ T H₂) ∧ (VZ T H₁ = VZ T H₂ ↔ (OrdLE T H₁ H₂ ∧ OrdLE T H₂ H₁))


@[expose] def A_5_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ →
      (∀ H : Subgroup G, InHvT T H → OrdLE T H H) ∧
      (∀ H₁ H₂ : Subgroup G, InHvT T H₁ → InHvT T H₂ → OrdLE T H₁ H₂ → OrdLE T H₂ H₁ → H₁ = H₂) ∧
      (∀ H₁ H₂ H₃ : Subgroup G, InHvT T H₁ → InHvT T H₂ → InHvT T H₃ →
        OrdLE T H₁ H₂ → OrdLE T H₂ H₃ → OrdLE T H₁ H₃) ∧
      (∀ M : Subgroup G, InMT T M → InHvT T M)


@[expose] def A_5_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ → ∀ H M : Subgroup G, InHT T H → InMT T M →
      OrdLE T H M →
      ∀ V : Subgroup G, V ≠ ⊥ →
        V = Subgroup.closure {x | ∃ h ∈ H ⊓ M, ∃ z ∈ V ⊓ omegaOne 2 (centerOf T), x = h * z * h⁻¹} →
        (V.subgroupOf M).Normal → V ≤ M → H ≤ M


@[expose] def A_5_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ →
      (∀ M : Subgroup G, InMT T M → (∀ M' : Subgroup G, InMT T M' → OrdLE T M M' → M' = M) →
        (∀ X : Subgroup G, InHT T X → X ≤ M → M = X ⊔ (M ⊓ centralizerOf (VZ T M)) →
          IsUniqueMaxTwoLocalOver X M) ∧
        (∀ V : Subgroup G,
          (V = VZ T M ∨
            (V = Subgroup.closure {x | ∃ m ∈ M, ∃ z ∈ V ⊓ omegaOne 2 (centerOf T), x = m * z * m⁻¹} ∧
              (∀ M' : Subgroup G, InMT T M' →
                (∀ M'' : Subgroup G, InMT T M'' → OrdLE T M' M'' → M'' = M') → M' = M))) →
          quasithinGenFitting (M ⊓ ChA.normalizerOf (T ⊓ centralizerOf V)) = T ⊓ centralizerOf V ∧
            IsTwoReduced (M ⊓ ChA.normalizerOf (T ⊓ centralizerOf V)) V ∧
            (∀ m ∈ M, ∃ n ∈ M ⊓ ChA.normalizerOf (T ⊓ centralizerOf V), ∀ v ∈ V, m * v * m⁻¹ = n * v * n⁻¹) ∧
            (V ≠ ⊥ → IsUniqueMaxTwoLocalOver (M ⊓ ChA.normalizerOf (T ⊓ centralizerOf V)) M))) ∧
      (∀ H : Subgroup G, InHT T H →
        ((InHvT T H ∧ ∀ H' : Subgroup G, InHvT T H' → OrdLE T H H' → H' = H) ↔
          (InMT T H ∧ ∀ M' : Subgroup G, InMT T M' → OrdLE T H M' → M' = H)))


@[expose] def A_5_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ → ∀ H K : Subgroup G, InHT T H → InHT T K →
      (H ≤ K → OrdLE T H K) ∧ (OrdLE T H K → OrdLE T K H → VZ T H = VZ T K)


@[expose] def A_5_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → IsEvenCharacteristic G →
    ∀ T : Subgroup G, IsSylowIn 2 T ⊤ → ∀ H K : Subgroup G, InHT T H → InHT T K →
      (∀ H' : Subgroup G, InHT T H' → VZ T H ≤ VZ T H' → VZ T H' = VZ T H) →
      (VZ T H ≤ VZ T K → K ≤ ChA.normalizerOf (VZ T H)) ∧
      (OrdLE T H K → K ≤ ChA.normalizerOf (VZ T H)) ∧
      IsUniqueMaxTwoLocalOver H (ChA.normalizerOf (VZ T H)) ∧
      (InMT T (ChA.normalizerOf (VZ T H)) ∧
        ∀ M' : Subgroup G, InMT T M' → OrdLE T (ChA.normalizerOf (VZ T H)) M' →
          M' = ChA.normalizerOf (VZ T H))


end CFSG.ASVolI
