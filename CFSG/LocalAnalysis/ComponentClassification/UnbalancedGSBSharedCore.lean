module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup
open scoped Pointwise commutatorElement

variable {X : Type*} [Group X]

theorem normalizer_le_normalizer_map_of_characteristic (J : Subgroup X) (K : Subgroup J)
    [hK : K.Characteristic] :
    normalizer (J : Set X) ≤ normalizer (K.map J.subtype : Set X) := by
  apply le_normalizer_iff.mpr
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
  have hmap := mem_normalizer_iff_map_conj_eq.mp hg
  let e : J ≃* J := ((MulAut.conj g).subgroupMap J).trans (MulEquiv.subgroupCongr hmap)
  have hey : e y ∈ K := by
    rw [← characteristic_iff_map_eq.mp hK e]
    exact mem_map_of_mem e.toMonoidHom hy
  exact mem_map.mpr ⟨e y, hey, rfl⟩

theorem odd_card_map_pPrimeCore_two [Finite X] (J : Subgroup X) :
    Odd (Nat.card ((pPrimeCore 2 J).map J.subtype)) := by
  rw [← Nat.card_congr ((pPrimeCore 2 J).equivMapOfInjective _ J.subtype_injective).toEquiv]
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem le_pPrimeCore_two_of_normal_odd {G : Type*} [Group G] {S : Subgroup G} (hS : S.Normal)
    (hodd : Odd (Nat.card S)) : S ≤ pPrimeCore 2 G :=
  le_sSup ⟨hS, Nat.coprime_two_left.mpr hodd⟩

theorem inf_le_map_pPrimeCore_two [Finite X] {J Y : Subgroup X}
    (hJY : J ≤ normalizer (Y : Set X)) (hY : Odd (Nat.card Y)) :
    J ⊓ Y ≤ (pPrimeCore 2 J).map J.subtype := by
  have hnormal : ((J ⊓ Y).subgroupOf J).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf, mem_inf] at hn ⊢
    simp only [coe_mul, coe_inv]
    exact ⟨mul_mem (mul_mem g.2 hn.1) (inv_mem g.2),
      (mem_normalizer_iff.mp (hJY g.2) n).mp hn.2⟩
  have hodd : Odd (Nat.card ((J ⊓ Y).subgroupOf J)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : J ⊓ Y ≤ J)).toEquiv]
    exact Odd.of_dvd_nat hY (card_dvd_of_le inf_le_right)
  have hle := map_mono (f := J.subtype) (le_pPrimeCore_two_of_normal_odd hnormal hodd)
  rwa [map_subgroupOf_eq_of_le inf_le_left] at hle

theorem mem_sup_iff_exists_mul {H K : Subgroup X} (hHK : H ≤ normalizer (K : Set X)) {x : X} :
    x ∈ H ⊔ K ↔ ∃ h ∈ H, ∃ k ∈ K, h * k = x := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right H K hHK]
  exact Set.mem_mul


namespace SharedInvolutionData


end SharedInvolutionData


end CFSG.ComponentClassification.UnbalancedGS
