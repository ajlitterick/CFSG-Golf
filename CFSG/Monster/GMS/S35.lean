module

public import CFSG.Monster.GMS.S347
public import CFSG.Monster.GMS.S342

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

section Defs

variable {G : Type*} [Group G]

inductive GMSType
  | twoA
  | twoB
  | threeA
  | threeC
  | fourA
  | fourB
  | fiveA
  | sixA
  deriving DecidableEq

@[expose] def typeSet (a z₀ x : G) : GMSType → Set G
  | .twoA => twoANbr a x
  | .twoB => twoBNbr a z₀ x
  | .fourA => fourANbr a z₀ x
  | .fourB => fourBNbr a x
  | .sixA => sixANbr a x
  | .threeA => {y | y ∈ oddNbr a z₀ x ∧ OddNbrType z₀ x y 0}
  | .threeC => {y | y ∈ oddNbr a z₀ x ∧ OddNbrType z₀ x y 1}
  | .fiveA => {y | y ∈ oddNbr a z₀ x ∧ OddNbrType z₀ x y 2}

@[expose] def gammaNbr (a z₀ x : G) : Set G := insert x (⋃ K, typeSet a z₀ x K)


theorem isConj_of_mem_typeSet {a z₀ x y : G} {K : GMSType} (h : y ∈ typeSet a z₀ x K) :
    IsConj a y := by
  cases K <;> first
    | exact h.1.1
    | exact h.1

theorem commute_of_mul_self {p b : G} (hp : p * p = 1) (hb : b * b = 1)
    (hpb : (p * b) * (p * b) = 1) : p * b = b * p := by
  have hpi : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have h1 : p * b = (p * b)⁻¹ := eq_inv_of_mul_eq_one_left hpb
  rw [h1, mul_inv_rev, hpi, hbi]

end Defs


section Cover

variable {G : Type*} [Group G]

@[expose] def GammaCover (a z₀ : G) : Prop :=
  ∀ x y : G, IsConj a x → IsConj a y → y ∈ gammaNbr a z₀ x

@[expose] def OddPairsCommonTwoB (a z₀ : G) : Prop :=
  ∀ x y : G, IsConj a x → IsConj a y → y ≠ x → Odd (orderOf (x * y)) → y ∈ oddNbr a z₀ x

end Cover

section OneSix

variable {G : Type} [Group G] {d₀ : B}


theorem exists_orderOf_eq_two_pow
    [Finite G] (hSLS : SLSStatement d₀) (hTV : TableVIn G)
    (hL : LeechStatement) {a z₀ : G} (hG : GMSF1Type d₀ a z₀) {x w : G} (hxA : IsConj a x)
    (hw : IsConj z₀ w) (haw : a * w = w * a) (hwa : IsConj a (a * w))
    (hxw : x ∈ Subgroup.centralizer ({w} : Set G)) : ∃ k, orderOf (a * x) = 2 ^ k := by
  have haQ : a ∈ leechQ w := mem_leechQ_of_isConj_mul hSLS hTV hL hG (IsConj.refl a) hw haw hwa
  have hxx : x * x = 1 :=
    mul_self_eq_one_of_orderOf ((orderOf_eq_of_isConj hxA).symm.trans hG.1.1)
  have hsq : (a * x) ^ 2 ∈ leechQ w := by
    have h1 : x * a * x⁻¹ ∈ leechQ w := conj_mem_leechQ hxw haQ
    have e : (a * x) ^ 2 = a * (x * a * x⁻¹) := by
      rw [pow_two, inv_eq_of_mul_eq_one_right hxx]; group
    rw [e]
    exact mul_mem haQ h1
  have hp : IsPGroup 2 ↥(leechQ w) := IsPGroup.of_card (hG.2.of_isConj hw).card_leechQ
  obtain ⟨m, hm⟩ := hp ⟨(a * x) ^ 2, hsq⟩
  have hm' : (a * x) ^ (2 ^ (m + 1)) = 1 := by
    have := congrArg Subtype.val hm
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
    rw [pow_succ', pow_mul]
    exact this
  have hdvd : orderOf (a * x) ∣ 2 ^ (m + 1) := orderOf_dvd_of_pow_eq_one hm'
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨k, hk⟩


end OneSix

end CFSG.Monster.GMS
