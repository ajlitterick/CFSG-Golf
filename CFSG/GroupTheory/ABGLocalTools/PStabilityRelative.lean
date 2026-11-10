module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
import CFSG.GroupTheory.ABGLocalTools.PStabilityDGroup
import CFSG.GroupTheory.ABGLocalTools.PStabilitySignalizer
import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
import CFSG.GroupTheory.ABGDGroups.WreathedDGroups
import CFSG.GroupTheory.QuasiDihedralFusion.Structure
import CFSG.GroupTheory.QuasiDihedralFusion.Transport

public section

open Subgroup

namespace CFSG.ABGLocalTools

open CFSG.QuasiDihedralFusion

variable {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]


section Wreathed

omit [Fact p.Prime] in
theorem oddCore_map_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (e : X ≃* Y) : (oddCore X).map e.toMonoidHom = oddCore Y := by
  apply le_antisymm
  · exact le_sSup ⟨(oddCore_normal X).map _ e.surjective,
      by rw [card_map_of_injective e.injective]; exact odd_card_oddCore⟩
  · have hle : (oddCore Y).map e.symm.toMonoidHom ≤ oddCore X :=
      le_sSup ⟨(oddCore_normal Y).map _ e.symm.surjective,
        by rw [card_map_of_injective e.symm.injective]; exact odd_card_oddCore⟩
    intro y hy
    exact ⟨e.symm y, hle ⟨y, hy, rfl⟩, by simp⟩

omit [Fact p.Prime] in
theorem oddCore_quotient_oddCore_eq_bot : oddCore (H ⧸ oddCore H) = ⊥ := by
  set N := (oddCore (H ⧸ oddCore H)).comap (QuotientGroup.mk' (oddCore H)) with hN
  have hNn : N.Normal := (oddCore_normal _).comap _
  have hNodd : Odd (Nat.card N) := by
    rw [hN, card_comap_mk']
    exact odd_card_oddCore.mul odd_card_oddCore
  have hNO : N ≤ oddCore H := le_oddCore_of_normal hNn hNodd
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  have : h ∈ oddCore H := hNO hx
  rw [mem_bot, QuotientGroup.eq_one_iff]
  exact this


end Wreathed

end CFSG.ABGLocalTools
