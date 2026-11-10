module

public import CFSG.ClassicalInvolution.AschTight.Hall196Main
public import CFSG.ClassicalInvolution.AschTight.Hall196Wr

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem isSylow2In_sup_of_normalizes {W Y P : Subgroup G} (hP : IsSylow2In P Y)
    (hW2 : IsPGroup 2 W) (hWY : W ≤ Subgroup.normalizer (Y : Set G))
    (hWP : W ≤ Subgroup.normalizer (P : Set G)) (hWYP : W ⊓ Y ≤ P) :
    IsSylow2In (P ⊔ W) (W ⊔ Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨sup_le (hP.1.trans le_sup_right) le_sup_left,
    IsPGroup.to_sup_of_normal_left' hP.2.1 hW2 hWP, fun T hT hT2 hle => ?_⟩
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) :=
    hT.trans (sup_le hWY Subgroup.le_normalizer)
  have h1 := card_sup_mul_card_inf' (A := Y) (C := T) hTY
  have h2 := card_sup_mul_card_inf' (A := Y) (C := W) hWY
  have h3 := card_sup_mul_card_inf' (A := P) (C := W) hWP
  have h4 : Nat.card ↥(Y ⊔ T) ≤ Nat.card ↥(Y ⊔ W) :=
    Subgroup.card_le_of_le (sup_le le_sup_left (sup_comm W Y ▸ hT))
  have h5 : Nat.card ↥(Y ⊓ T) ≤ Nat.card P :=
    hP.natCard_le (hT2.to_le inf_le_right) inf_le_left
  have h6 : Y ⊓ W = P ⊓ W := by
    refine le_antisymm (fun x hx => ⟨hWYP ⟨hx.2, hx.1⟩, hx.2⟩) (fun x hx => ⟨hP.1 hx.1, hx.2⟩)
  rw [h6] at h2
  have hd : 0 < Nat.card ↥(P ⊓ W) := Nat.card_pos
  have hY : 0 < Nat.card Y := Nat.card_pos
  have key : Nat.card Y * Nat.card ↥(P ⊓ W) * Nat.card T ≤
      Nat.card Y * Nat.card ↥(P ⊓ W) * Nat.card ↥(P ⊔ W) := by
    calc Nat.card Y * Nat.card ↥(P ⊓ W) * Nat.card T
        = (Nat.card Y * Nat.card T) * Nat.card ↥(P ⊓ W) := by ring
      _ = Nat.card ↥(Y ⊔ T) * Nat.card ↥(Y ⊓ T) * Nat.card ↥(P ⊓ W) := by rw [h1]
      _ ≤ Nat.card ↥(Y ⊔ W) * Nat.card P * Nat.card ↥(P ⊓ W) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul h4 h5)
      _ = (Nat.card ↥(Y ⊔ W) * Nat.card ↥(P ⊓ W)) * Nat.card P := by ring
      _ = Nat.card Y * (Nat.card P * Nat.card W) := by rw [h2]; ring
      _ = Nat.card Y * (Nat.card ↥(P ⊔ W) * Nat.card ↥(P ⊓ W)) := by rw [h3]
      _ = Nat.card Y * Nat.card ↥(P ⊓ W) * Nat.card ↥(P ⊔ W) := by ring
  have hcard := Nat.le_of_mul_le_mul_left key (Nat.mul_pos hY hd)
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

omit [Finite G] in
theorem le_normalizer_inf {S Y W : Subgroup G} (hWS : W ≤ S)
    (hWY : W ≤ Subgroup.normalizer (Y : Set G)) :
    W ≤ Subgroup.normalizer ((S ⊓ Y : Subgroup G) : Set G) := by
  intro w hw
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hwS := hWS hw
  have hwY := Subgroup.mem_normalizer_iff.mp (hWY hw) x
  constructor
  · rintro ⟨hxS, hxY⟩
    exact ⟨S.mul_mem (S.mul_mem hwS hxS) (S.inv_mem hwS), hwY.mp hxY⟩
  · rintro ⟨hxS, hxY⟩
    refine ⟨?_, hwY.mpr hxY⟩
    have e : x = w⁻¹ * (w * x * w⁻¹) * w := by group
    rw [e]
    exact S.mul_mem (S.mul_mem (S.inv_mem hwS) hxS) hwS


end CFSG.ClassicalInvolution.Disconnected.AschTight.Hall196
