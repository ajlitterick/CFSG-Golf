module

public import CFSG.Quasithin.Background.RonanE43Out
public import CFSG.Quasithin.Background.E2TwoProofSporGen
public import CFSG.Quasithin.Background.RonanE43Basic

public section

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.E2P B6
  CFSG.Quasithin.E2P.SporB

variable {G : Type} [Group G]

theorem card_sup_eq_relIndex_mul {P T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (P : Set G)) :
    Nat.card ↥(P ⊔ T) = P.relIndex T * Nat.card P := by
  haveI := Subgroup.normal_subgroupOf_of_le_normalizer hT
  haveI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient T P hT
  have h1 : Nat.card (↥T ⧸ P.subgroupOf T) =
      Nat.card (↥(T ⊔ P) ⧸ P.subgroupOf (T ⊔ P)) := Nat.card_congr e.toEquiv
  have h2 : P.relIndex (T ⊔ P) * Nat.card ↥(P ⊓ (T ⊔ P)) = Nat.card ↥(T ⊔ P) :=
    Subgroup.relIndex_mul_card (H := P) (K := T ⊔ P)
  rw [inf_eq_left.mpr le_sup_right] at h2
  rw [sup_comm, ← h2]
  have h3 : P.relIndex (T ⊔ P) = P.relIndex T := by
    unfold Subgroup.relIndex Subgroup.index
    exact h1.symm
  rw [h3]

variable [Finite G]

theorem card_le_two_mul_pCoreOf {T H : Subgroup G} (hTH : T ≤ H) (hT2 : IsPGroup 2 T)
    (h3 : Nat.card H = 3 * Nat.card T) : Nat.card T ≤ 2 * Nat.card (pCoreOf 2 H) := by
  set K : Subgroup ↥H := T.subgroupOf H with hK
  have hKcard : Nat.card K = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTH).toEquiv
  have hTpos : 0 < Nat.card T := Nat.card_pos
  have hKidx : K.index = 3 := by
    have h1 := Subgroup.card_mul_index K
    rw [hKcard] at h1
    have : Nat.card T * K.index = Nat.card T * 3 := by rw [h1, h3]; ring
    exact Nat.eq_of_mul_eq_mul_left hTpos this
  have hKp : IsPGroup 2 K := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  set C : Subgroup ↥H := K.normalCore with hC
  haveI : C.Normal := Subgroup.normalCore_normal K
  have hCp : IsPGroup 2 C := hKp.to_le (Subgroup.normalCore_le K)
  have hCle : C.map H.subtype ≤ pCoreOf 2 H :=
    Subgroup.map_mono (CFSG.LieType.BorelTits.le_pCore 2 inferInstance hCp)
  have hCcard : Nat.card C ≤ Nat.card (pCoreOf 2 H) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective (K := C)]
    exact Subgroup.card_le_of_le hCle
  have hidx : C.index ≤ 6 := by
    have := Subgroup.index_normalCore_le_factorial_index K
    rw [hKidx] at this
    simpa [Nat.factorial] using this
  have hH : Nat.card C * C.index = Nat.card H := Subgroup.card_mul_index C
  have hHcard : Nat.card H = Nat.card ↥H := rfl
  have h6 : Nat.card H ≤ 6 * Nat.card C := by
    calc Nat.card H = Nat.card C * C.index := hH.symm
      _ ≤ Nat.card C * 6 := Nat.mul_le_mul_left _ hidx
      _ = 6 * Nat.card C := by ring
  omega


end CFSG.Quasithin.RonanE43
