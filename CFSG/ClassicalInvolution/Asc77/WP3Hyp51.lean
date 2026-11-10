module

public import CFSG.ClassicalInvolution.Asc77.WP2Defs
public import CFSG.ClassicalInvolution.Asc77.WP3Fuzzy

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Disconnected

section Induced

variable {H : Type} [Group H]

@[expose] def conjOnNormalizer (L : Subgroup H) :
    ↥(Subgroup.normalizer (L : Set H)) →* MulAut ↥L where
  toFun x :=
    { toFun := fun y => ⟨(x : H) * y * (x : H)⁻¹, (Subgroup.mem_normalizer_iff.mp x.2 y).mp y.2⟩
      invFun := fun y => ⟨(x : H)⁻¹ * y * (x : H), (Subgroup.mem_normalizer_iff.mp x.2 _).mpr (by
        have e : (x : H) * ((x : H)⁻¹ * y * (x : H)) * (x : H)⁻¹ = y := by group
        rw [e]
        exact y.2)⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun y z => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext y
    simp
  map_mul' := fun x x' => by
    ext y
    simp [mul_assoc]

@[expose] def inducedAutOn (L : Subgroup H) : Subgroup (MulAut ↥L) :=
  (conjOnNormalizer L).range

@[expose] def toInducedAutOn (L : Subgroup H) :
    ↥(Subgroup.normalizer (L : Set H)) →* ↥(inducedAutOn L) :=
  (conjOnNormalizer L).rangeRestrict

@[expose] def inducedImage (L : Subgroup H) (B : Subgroup H) : Subgroup ↥(inducedAutOn L) :=
  (B.subgroupOf (Subgroup.normalizer (L : Set H))).map (toInducedAutOn L)

end Induced

section Hyp51

variable {G : Type} [Group G]

@[expose] def MovedByAll (B : Subgroup G) (c : G) (L : Subgroup (OddQuot c)) : Prop :=
  ∀ x ∈ modOdd c B, x ∉ modOdd c (Subgroup.zpowers c) → ∃ y ∈ L, x * y ≠ y * x

@[expose] def Hyp51At (B : Subgroup G) (c : G) : Prop :=
  (∀ L₁ L₂ : Subgroup (OddQuot c), CFSG.IsComponent L₁ → CFSG.IsComponent L₂ →
      MovedByAll B c L₁ → MovedByAll B c L₂ → L₁ = L₂) ∧
    ∀ L : Subgroup (OddQuot c), CFSG.IsComponent L → MovedByAll B c L →
      alphaOf (inducedImage L (modOdd c B)) = ⊥

@[expose] def Hyp51 (B : Subgroup G) : Prop :=
  IsElemAbelian 2 B ∧ Nat.card B = 8 ∧ ∀ c ∈ B, c ≠ 1 → Hyp51At B c

end Hyp51

@[expose] def Lemma52 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B : Subgroup G), Hyp51 B → RankThreeBalance B

section Frames


end Frames

end CFSG.ClassicalInvolution.Asc77
