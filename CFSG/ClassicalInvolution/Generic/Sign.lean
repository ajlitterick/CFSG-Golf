module

public import CFSG.ClassicalInvolution.Generic.LineModelLinear
public import CFSG.ClassicalInvolution.Generic.LineModelUnitary
public import CFSG.ClassicalInvolution.Phan.Torus

public section

namespace CFSG.ClassicalInvolution.Generic

open scoped MatrixGroups
open CFSG.LieType.Steinberg CFSG.LieType.BorelTits

section Tori

theorem card_diagTorus2_linear (F : Type) [Field F] [Finite F] :
    Nat.card (WeakCT.diagTorus2 F) = Nat.card F - 1 := by
  rw [WeakCT.diagTorus2,
    Nat.card_congr (MonoidHom.ofInjective (WeakCT.torusHom_injective (K := F))).toEquiv.symm,
    Nat.card_units]

theorem card_diagTorus2_unitary (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) :
    Nat.card (Phan.diagTorus2 K p f) = p ^ f + 1 := by
  rw [Phan.diagTorus2,
    Nat.card_congr
      (MonoidHom.ofInjective (torusTwo_injective (unitaryInvolution K p f))).toEquiv.symm,
    Phan.card_normOne hK]

end Tori

section Pairs

variable {F : Type} [Field F] [Finite F] {G : Type} [Group G]

theorem LinearA2Pair.card_centPart_left {E K L : Subgroup G} (h : LinearA2Pair F E K L) :
    Nat.card (centPart K E) = Nat.card F - 1 := by
  obtain ⟨θ, hker, -, -, hHK, -⟩ := h
  rw [hHK, WeakCT.map_D12,
    Subgroup.card_map_of_injective (WeakCT.comp_blockSL_injective hker (by omega) (by omega)),
    card_diagTorus2_linear]

theorem LinearA2Pair.card_centPart_right {E K L : Subgroup G} (h : LinearA2Pair F E K L) :
    Nat.card (centPart L E) = Nat.card F - 1 := by
  obtain ⟨θ, hker, -, -, -, hHL⟩ := h
  rw [hHL, WeakCT.map_D23,
    Subgroup.card_map_of_injective (WeakCT.comp_blockSL_injective hker (by omega) (by omega)),
    card_diagTorus2_linear]

variable {K' : Type} [Field K'] [Finite K'] {p f : ℕ} [Fact p.Prime] [CharP K' p]

theorem UnitaryA2Pair.card_centPart_left (hK : Nat.card K' = (p ^ f) ^ 2) {E P Q : Subgroup G}
    (h : UnitaryA2Pair K' p f E P Q) : Nat.card (centPart P E) = p ^ f + 1 := by
  obtain ⟨θ, hker, -, -, hHP, -⟩ := h
  rw [hHP, Phan.map_D12, Subgroup.card_map_of_injective (Phan.comp_embSUid_injective hK hker 2),
    card_diagTorus2_unitary K' p f hK]

theorem UnitaryA2Pair.card_centPart_right (hK : Nat.card K' = (p ^ f) ^ 2) {E P Q : Subgroup G}
    (h : UnitaryA2Pair K' p f E P Q) : Nat.card (centPart Q E) = p ^ f + 1 := by
  obtain ⟨θ, hker, -, -, -, hHQ⟩ := h
  rw [hHQ, Phan.map_D23, Subgroup.card_map_of_injective (Phan.comp_embSUid_injective hK hker 0),
    card_diagTorus2_unitary K' p f hK]

variable (F) in
@[expose] def LinearPair (E K L : Subgroup G) : Prop :=
  LinearA2Pair F E K L ∨ LinearA2Pair F E L K

variable (K' p f) in
@[expose] def UnitaryPair (E K L : Subgroup G) : Prop :=
  UnitaryA2Pair K' p f E K L ∨ UnitaryA2Pair K' p f E L K

theorem LinearPair.card_centPart {E K L : Subgroup G} (h : LinearPair F E K L) :
    Nat.card (centPart K E) = Nat.card F - 1 ∧ Nat.card (centPart L E) = Nat.card F - 1 := by
  rcases h with h | h
  · exact ⟨h.card_centPart_left, h.card_centPart_right⟩
  · exact ⟨h.card_centPart_right, h.card_centPart_left⟩

theorem UnitaryPair.card_centPart (hK : Nat.card K' = (p ^ f) ^ 2) {E K L : Subgroup G}
    (h : UnitaryPair K' p f E K L) :
    Nat.card (centPart K E) = p ^ f + 1 ∧ Nat.card (centPart L E) = p ^ f + 1 := by
  rcases h with h | h
  · exact ⟨h.card_centPart_left hK, h.card_centPart_right hK⟩
  · exact ⟨h.card_centPart_right hK, h.card_centPart_left hK⟩

end Pairs

section Sign


end Sign

end CFSG.ClassicalInvolution.Generic
