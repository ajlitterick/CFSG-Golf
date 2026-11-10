module

public import CFSG.Quasithin.EmptyFaithful.S1422AutM12
public import CFSG.Quasithin.EmptyFaithful.S1422Sz
public import CFSG.Quasithin.EmptyFaithful.S142Statements

public section

namespace CFSG.Quasithin

open CFSG.Open

theorem false_of_isL2Quot_one_of_card {G : Type*} [Group G] {H : Subgroup G}
    (hSz : Nat.card ↥(Sz 0) = 20)
    (h : Nonempty (oTwoQuot ↥H ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥H ≃* ↥(Sz 0)))
    (h1 : IsL2Quot 1 (oTwoQuot ↥H)) : False := by
  have h6 : Nat.card (oTwoQuot ↥H) = 6 := by
    rw [h1.card le_rfl]; norm_num
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · have := Nat.card_congr e.toEquiv
    rw [h6, Nat.card_eq_fintype_card (α := DihedralGroup 5), DihedralGroup.card] at this
    omega
  · have := Nat.card_congr e.toEquiv
    rw [h6, hSz] at this
    omega

theorem false_of_perm_three_of_card {G : Type*} [Group G] {H : Subgroup G}
    (hSz : Nat.card ↥(Sz 0) = 20) (h : Nonempty (oTwoQuot ↥H ≃* Equiv.Perm (Fin 3)))
    (h' : Nonempty (oTwoQuot ↥H ≃* DihedralGroup 5) ∨ Nonempty (oTwoQuot ↥H ≃* ↥(Sz 0))) :
    False := by
  obtain ⟨e⟩ := h
  have h6 : Nat.card (oTwoQuot ↥H) = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]; rfl
  rcases h' with ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩
  · have := Nat.card_congr e'.toEquiv
    rw [h6, Nat.card_eq_fintype_card (α := DihedralGroup 5), DihedralGroup.card] at this
    omega
  · have := Nat.card_congr e'.toEquiv
    rw [h6, hSz] at this
    omega


end CFSG.Quasithin
