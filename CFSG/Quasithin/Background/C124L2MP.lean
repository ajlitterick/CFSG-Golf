module

public import CFSG.Quasithin.Background.C126NatDSimple
public import CFSG.Quasithin.Background.C126A5Core1
public import CFSG.Quasithin.Background.B2FactorizationSolvable
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedSylow

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.L2

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 CFSG.LieType.BorelTits
  CFSG.Quasithin.C126.A5
open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_sup_of_normalizing {Y T : Subgroup G}
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) (hT2 : IsPGroup 2 T)
    (hsyl : IsSylowTwoOf (T ⊓ Y) Y) : IsSylowTwoOf T (Y ⊔ T) := by
  refine ⟨le_sup_right, hT2, ?_⟩
  have h1 := Subgroup.relIndex_mul_card T (Y ⊔ T)
  rw [inf_eq_left.2 (le_sup_right : T ≤ Y ⊔ T)] at h1
  have h2 := card_sup_mul_card_inf_of_le_normalizer hTY
  have h3 := Subgroup.relIndex_mul_card (Y ⊓ T) Y
  rw [inf_eq_left.2 (inf_le_left : Y ⊓ T ≤ Y)] at h3
  have hpos : 0 < Nat.card ↥(Y ⊓ T) := Nat.card_pos
  have hposT : 0 < Nat.card T := Nat.card_pos
  have key : T.relIndex (Y ⊔ T) = (Y ⊓ T).relIndex Y := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hposT hpos)
    calc T.relIndex (Y ⊔ T) * (Nat.card T * Nat.card ↥(Y ⊓ T))
        = Nat.card ↥(Y ⊔ T) * Nat.card ↥(Y ⊓ T) := by rw [← h1]; ring
      _ = Nat.card Y * Nat.card T := h2
      _ = (Y ⊓ T).relIndex Y * (Nat.card T * Nat.card ↥(Y ⊓ T)) := by rw [← h3]; ring
  have hidx : (T.subgroupOf (Y ⊔ T)).index = (Y ⊓ T).relIndex Y := key
  rw [hidx]
  have hs := hsyl.2.2
  rwa [inf_comm] at hs

theorem autI_le_normalizer_of_le_normalizer {H K V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hK : H ≤ Subgroup.normalizer (K : Set G)) :
    autI hV H ≤ Subgroup.normalizer (autI hV K : Set (MulAut (IntMod V hV))) := by
  intro φ hφ
  obtain ⟨g, hgH, rfl⟩ := (mem_autI hV).1 hφ
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨k, hkK, rfl⟩ := (mem_autI hV).1 hn
  refine (mem_autI hV).2 ⟨g * k * g⁻¹, ?_, by simp [map_mul, map_inv]⟩
  have := (Subgroup.mem_normalizer_iff.1 (hK hgH) (k : G)).1 hkK
  simpa using this

section Dickson

variable {Y V : Subgroup G} {F : Type} [Field F] [Finite F]

theorem card_eq_four_of_sylow (hV : IsElemAbelian 2 V) (hF : Nat.card F = 4)
    {S : Subgroup (MulAut (IntMod V hV))} (e : ↥(autI hV Y) ≃* SL(2, F))
    (hS : IsSylowTwoOf S (autI hV Y)) : Nat.card S = 4 := by
  have hF4 : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  rw [C126.Nat.card_sylow_of_equiv_sl2 (by norm_num) hF4 e hS]
  norm_num

omit [Finite G] in
theorem card_sl2_four (hF : Nat.card F = 4) : Nat.card SL(2, F) = 60 := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF]
  norm_num

theorem not_le_normalizer_sylow (hV : IsElemAbelian 2 V) (hF : Nat.card F = 4)
    {S : Subgroup (MulAut (IntMod V hV))} (e : ↥(autI hV Y) ≃* SL(2, F))
    (hS : IsSylowTwoOf S (autI hV Y)) :
    ¬ autI hV Y ≤ Subgroup.normalizer (S : Set (MulAut (IntMod V hV))) := by
  intro hN
  have hF4 : Nat.card F = 2 ^ 2 := by rw [hF]; norm_num
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by norm_num) hF4
  have hsimple : IsSimpleGroup SL(2, F) := C126.Nat.isSimpleGroup_sl2 (by omega)
  have hsY : IsSimpleGroup ↥(autI hV Y) := e.isSimpleGroup
  have hSY : S ≤ autI hV Y := hS.1
  have hnorm : (S.subgroupOf (autI hV Y)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSY).2 hN
  have hc4 := card_eq_four_of_sylow hV hF e hS
  have hcS : Nat.card (S.subgroupOf (autI hV Y)) = 4 := by
    rw [← hc4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSY).toEquiv
  have h60 : Nat.card ↥(autI hV Y) = 60 := by
    rw [Nat.card_congr e.toEquiv, card_sl2_four hF]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.subgroupOf (autI hV Y)) with h | h
  · rw [h, Subgroup.card_bot] at hcS
    omega
  · rw [h, Subgroup.card_top, h60] at hcS
    omega


end Dickson

end CFSG.Quasithin.C124.L2
