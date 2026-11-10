module

public import CFSG.Quasithin.Recognition.GoldschmidtGluing

public section

namespace CFSG.Quasithin

namespace GoldAmalgam

@[expose] def ofSubgroups {A B : Type*} [Group A] [Group B] (P : Subgroup A) (Q : Subgroup B)
    (e : P ≃* Q) : GoldAmalgam A P B :=
  ⟨P.subtype, Q.subtype.comp e.toMonoidHom, P.subtype_injective,
    Q.subtype_injective.comp e.injective⟩


section Orders

variable {A C B : Type*} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

theorem card_edgeA_eq : Nat.card X.edgeA = Nat.card C :=
  Nat.card_congr (MonoidHom.ofInjective X.toA_injective).toEquiv.symm

theorem card_edgeB_eq : Nat.card X.edgeB = Nat.card C :=
  Nat.card_congr (MonoidHom.ofInjective X.toB_injective).toEquiv.symm

theorem card_A_eq (hA : X.edgeA.index = 3) : Nat.card A = 3 * Nat.card C := by
  have := X.edgeA.card_mul_index
  rw [card_edgeA_eq, hA] at this
  omega

theorem card_B_eq (hB : X.edgeB.index = 3) : Nat.card B = 3 * Nat.card C := by
  have := X.edgeB.card_mul_index
  rw [card_edgeB_eq, hB] at this
  omega

section FiniteC

variable [Finite C]


end FiniteC

end Orders

section Representation


variable {A C B : Type*} [Group A] [Group C] [Group B] [Finite A] [Finite C] [Finite B]
  (X : GoldAmalgam A C B)


end Representation


theorem sylow_index_eq_three_of_card {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) (k : ℕ)
    (hG : Nat.card G = 3 * 2 ^ k) : (S : Subgroup G).index = 3 := by
  have h3 : (3 * 2 ^ k).factorization 2 = k := by
    rw [Nat.factorization_mul (by norm_num) (by positivity), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    simp
  have hpos : 0 < 2 ^ k := by positivity
  have h1 := Sylow.card_eq_multiplicity S
  have h2 := (S : Subgroup G).card_mul_index
  rw [hG, h3] at h1
  rw [h1, hG] at h2
  have : 2 ^ k * (S : Subgroup G).index = 2 ^ k * 3 := by rw [h2]; ring
  exact Nat.eq_of_mul_eq_mul_left hpos this

section Soundness


end Soundness

section Closure


end Closure


section Headline


end Headline

end GoldAmalgam

end CFSG.Quasithin
