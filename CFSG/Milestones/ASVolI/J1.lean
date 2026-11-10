module

public import CFSG.Milestones.ASVolI.I7

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.ChIJK

open CFSG.Open CFSG.Blueprint
open scoped MatrixGroups

section Ru

variable {G : Type} [Group G]

@[expose] def IsSylowIn (p : ℕ) (B X : Subgroup G) : Prop :=
  B ≤ X ∧ IsPGroup p B ∧ ¬ p ∣ (B.subgroupOf X).index


@[expose] def ZRu (T : Subgroup G) : Subgroup G := centerOf T

@[expose] def HRu (T : Subgroup G) : Subgroup G := Subgroup.centralizer (ZRu T : Set G)

@[expose] def QRu (T : Subgroup G) : Subgroup G := pCoreOf 2 (HRu T)

@[expose] def URu (V T : Subgroup G) : Subgroup G := conjClosure V (HRu T)

@[expose] def SRu (L : Subgroup G) : Subgroup G := pCoreOf 2 L


@[expose] def IsSigmaL24Map (g : (Fin 2 → F4) ≃ₗ[ZMod 2] (Fin 2 → F4)) : Prop :=
  ∃ (A : Matrix.SpecialLinearGroup (Fin 2) F4) (i : ℕ), ∀ x : Fin 2 → F4,
    g x = (A : Matrix (Fin 2) (Fin 2) F4).mulVec (fun j => (frobenius F4 2)^[i] (x j))


end Ru

structure RuType (G : Type) [Group G] [Finite G] (L V T : Subgroup G) : Prop where
  L_eq : L = Subgroup.normalizer (V : Set G)
  S_special : IsSpecialGroup (SRu L)
  V_eq : V = centerOf (SRu L)
  V_E8 : IsElemAbelian 2 V ∧ Nat.card ↥V = 8
  LS_L32 : StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1
  V_natural : ∀ φ : ↥V ≃* ↥V, ∃ l ∈ L, ∀ v : ↥V, l⁻¹ * (v : G) * l = (φ v : G)
  SV_steinberg : V.relIndex (SRu L) = 2 ^ 8 ∧
    ∀ B : Subgroup G, V ≤ B → B ≤ SRu L → L ≤ Subgroup.normalizer (B : Set G) →
      B = V ∨ B = SRu L
  T_sylow : IsSylowTwoIn T ⊤
  T_choice : IsSylowTwoIn (T ⊓ Subgroup.normalizer (V : Set G)) L
  H_star : Nonempty (↥(HRu T) ⧸ CFSG.pCore 2 ↥(HRu T) ≃* Equiv.Perm (Fin 5))
  U_L24 : ∃ θ : (↥(HRu T) ⧸ CFSG.pCore 2 ↥(HRu T)) →*
      ((Fin 2 → F4) ≃ₗ[ZMod 2] (Fin 2 → F4)),
    Function.Injective θ ∧ (∀ h, IsSigmaL24Map (θ h)) ∧
    IsConjModuleIso (HRu T) (URu V T) (ZRu T) (Fin 2 → F4)
      (fun h v => θ (h : ↥(HRu T) ⧸ CFSG.pCore 2 ↥(HRu T)) v)
  Q_over_U : URu V T ≤ QRu T ∧ (URu V T).relIndex (QRu T) = 2 ^ 6 ∧
    (∀ x ∈ QRu T, x ^ 2 ∈ URu V T) ∧
    (∀ x ∈ QRu T, ∀ y ∈ QRu T, x * y * x⁻¹ * y⁻¹ ∈ URu V T) ∧
    ∀ A B : Subgroup G, URu V T ≤ A → A ≤ QRu T → URu V T ≤ B → B ≤ QRu T →
      HRu T ≤ Subgroup.normalizer (A : Set G) → HRu T ≤ Subgroup.normalizer (B : Set G) →
      A ⊔ B = QRu T → A ⊓ B = URu V T → A = URu V T ∨ B = URu V T

end CFSG.ASVolI.ChIJK
