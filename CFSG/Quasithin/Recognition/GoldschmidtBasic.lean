module

public import CFSG.LieType.BorelTits.Basic
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section General

instance gold_pCore_normal (p : ℕ) (G : Type*) [Group G] : (pCore p G).Normal := pCore_normal p

theorem gold_orderOf_conj {G : Type*} [Group G] (a x : G) : orderOf (a * x * a⁻¹) = orderOf x :=
  (SemiconjBy.orderOf_eq a (show SemiconjBy a x (a * x * a⁻¹) by
    simp [SemiconjBy, mul_assoc])).symm

theorem gold_relIndex_normalCore_dvd_two {A : Type*} [Group A] {H : Subgroup A}
    (hH : H.index = 3) : H.normalCore.relIndex H ∣ 2 := by
  have : H.FiniteIndex := ⟨by omega⟩
  have h1 : H.normalCore.index ∣ Nat.factorial H.index := H.index_normalCore_dvd_factorial_index
  have h2 := Subgroup.relIndex_mul_index H.normalCore_le
  rw [← h2, hH] at h1
  have h3 : H.normalCore.relIndex H * 3 ∣ 2 * 3 := by
    simpa [Nat.factorial] using h1
  exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h3

theorem gold_card_perm_fin_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl


theorem gold_mem_of_odd_orderOf_of_index_dvd_two {C : Type*} [Group C] {K : Subgroup C} [K.Normal]
    (hK : K.index ∣ 2) {x : C} (hx : Odd (orderOf x)) : x ∈ K := by
  have h1 : orderOf (QuotientGroup.mk x : C ⧸ K) ∣ 2 := by
    refine (orderOf_dvd_natCard _).trans ?_
    rw [← Subgroup.index_eq_card]
    exact hK
  have h2 : orderOf (QuotientGroup.mk x : C ⧸ K) ∣ orderOf x :=
    orderOf_map_dvd (QuotientGroup.mk' K) x
  have hcop : Nat.Coprime (orderOf x) 2 := Nat.coprime_two_right.mpr hx
  have h3 : orderOf (QuotientGroup.mk x : C ⧸ K) = 1 :=
    Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h2 h1)
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h3)

theorem gold_normalCore_quotient_equiv {A : Type*} [Group A] {H : Subgroup A} (hH : H.index = 3) :
    (H.normalCore.index = 3 ∧ Nonempty (A ⧸ H.normalCore ≃* Multiplicative (ZMod 3))) ∨
    (H.normalCore.index = 6 ∧ Nonempty (A ⧸ H.normalCore ≃* Equiv.Perm (Fin 3))) := by
  have hfin : H.FiniteIndex := ⟨by omega⟩
  have hrel : H.normalCore.relIndex H ∣ 2 := gold_relIndex_normalCore_dvd_two hH
  have hmul := Subgroup.relIndex_mul_index (H.normalCore_le)
  rw [hH] at hmul
  rcases (Nat.dvd_prime Nat.prime_two).mp hrel with h1 | h2
  · left
    have hidx : H.normalCore.index = 3 := by rw [← hmul, h1]
    refine ⟨hidx, ⟨?_⟩⟩
    have hc : Nat.card (A ⧸ H.normalCore) = 3 := by rw [← Subgroup.index_eq_card, hidx]
    refine mulEquivOfPrimeCardEq (p := 3) hc ?_
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  · right
    have hidx : H.normalCore.index = 6 := by rw [← hmul, h2]
    refine ⟨hidx, ⟨?_⟩⟩
    let φ : A →* Equiv.Perm (A ⧸ H) := MulAction.toPermHom A (A ⧸ H)
    have hker : H.normalCore = φ.ker := H.normalCore_eq_ker
    let f : A ⧸ H.normalCore →* Equiv.Perm (A ⧸ H) :=
      QuotientGroup.lift H.normalCore φ hker.le
    have hinj : Function.Injective f := by
      rw [injective_iff_map_eq_one]
      intro q hq
      induction q using QuotientGroup.induction_on with
      | H a =>
        have ha : φ a = 1 := hq
        have : a ∈ H.normalCore := by rw [hker]; exact ha
        exact (QuotientGroup.eq_one_iff a).mpr this
    have hcardQ : Nat.card (A ⧸ H) = 3 := by rw [← Subgroup.index_eq_card, hH]
    have hcardP : Nat.card (Equiv.Perm (A ⧸ H)) = 6 := by
      rw [Nat.card_perm, hcardQ]; rfl
    have hcardN : Nat.card (A ⧸ H.normalCore) = 6 := by rw [← Subgroup.index_eq_card, hidx]
    have : Finite (Equiv.Perm (A ⧸ H)) := Nat.finite_of_card_ne_zero (by rw [hcardP]; norm_num)
    have hbij : Function.Bijective f :=
      hinj.bijective_of_nat_card_le (by rw [hcardP, hcardN])
    let e : (A ⧸ H) ≃ Fin 3 := Finite.equivFinOfCardEq hcardQ
    exact (MulEquiv.ofBijective f hbij).trans e.permCongrHom


end General

structure GoldAmalgam (A C B : Type*) [Group A] [Group C] [Group B] where
  toA : C →* A
  toB : C →* B
  toA_injective : Function.Injective toA
  toB_injective : Function.Injective toB

namespace GoldAmalgam

variable {A C B : Type*} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def edgeA : Subgroup A := X.toA.range

@[expose] def edgeB : Subgroup B := X.toB.range

@[expose] def IsFaithful : Prop :=
  ∀ K : Subgroup C, (K.map X.toA).Normal → (K.map X.toB).Normal → K = ⊥

@[expose] def IsIndexThree : Prop := X.edgeA.index = 3 ∧ X.edgeB.index = 3

@[expose] def coreA : Subgroup C := X.edgeA.normalCore.comap X.toA

@[expose] def coreB : Subgroup C := X.edgeB.normalCore.comap X.toB

@[expose] def swap : GoldAmalgam B C A := ⟨X.toB, X.toA, X.toB_injective, X.toA_injective⟩

@[simp] theorem swap_toA : X.swap.toA = X.toB := rfl
@[simp] theorem swap_toB : X.swap.toB = X.toA := rfl
@[simp] theorem swap_edgeA : X.swap.edgeA = X.edgeB := rfl
@[simp] theorem swap_edgeB : X.swap.edgeB = X.edgeA := rfl
@[simp] theorem swap_coreA : X.swap.coreA = X.coreB := rfl
@[simp] theorem swap_coreB : X.swap.coreB = X.coreA := rfl

theorem swap_isFaithful_iff : X.swap.IsFaithful ↔ X.IsFaithful := by
  constructor
  · intro h K hA hB
    exact h K hB hA
  · intro h K hB hA
    exact h K hA hB


theorem toA_mem_edgeA (c : C) : X.toA c ∈ X.edgeA := ⟨c, rfl⟩

theorem coreA_normal : X.coreA.Normal := Subgroup.Normal.comap (Subgroup.normalCore_normal _) _


theorem map_coreA : X.coreA.map X.toA = X.edgeA.normalCore :=
  Subgroup.map_comap_eq_self (X.edgeA.normalCore_le)


theorem coreA_index_eq : X.coreA.index = X.edgeA.normalCore.relIndex X.edgeA := by
  unfold coreA edgeA
  rw [Subgroup.index_comap]


theorem coreA_index_dvd_two (hA : X.edgeA.index = 3) : X.coreA.index ∣ 2 := by
  rw [coreA_index_eq]
  exact gold_relIndex_normalCore_dvd_two hA

theorem coreB_index_dvd_two (hB : X.edgeB.index = 3) : X.coreB.index ∣ 2 :=
  X.swap.coreA_index_dvd_two hB

theorem odd_mem_coreA (h2 : X.coreA.index ∣ 2) {x : C} (hx : Odd (orderOf x)) : x ∈ X.coreA := by
  have := X.coreA_normal
  exact gold_mem_of_odd_orderOf_of_index_dvd_two h2 hx


theorem oddClosure_map_toA_normal (h2 : X.coreA.index ∣ 2) :
    ((Subgroup.closure {x : C | Odd (orderOf x)}).map X.toA).Normal := by
  rw [MonoidHom.map_closure]
  refine ⟨fun y hy a => ?_⟩
  induction hy using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    have hxK : X.toA x ∈ X.edgeA.normalCore := X.odd_mem_coreA h2 hx
    have h3 : a * X.toA x * a⁻¹ ∈ X.edgeA.normalCore :=
      (Subgroup.normalCore_normal _).conj_mem _ hxK a
    obtain ⟨z, hz⟩ := Subgroup.normalCore_le _ h3
    apply Subgroup.subset_closure
    refine ⟨z, ?_, hz⟩
    show Odd (orderOf z)
    have : orderOf z = orderOf x := by
      rw [← orderOf_injective X.toA X.toA_injective z, hz, gold_orderOf_conj,
        orderOf_injective X.toA X.toA_injective x]
    rw [this]
    exact hx
  | one => simp
  | mul y z _ _ hy hz =>
    have := mul_mem hy hz
    simpa [mul_assoc] using this
  | inv y _ hy =>
    have := inv_mem hy
    simpa [mul_assoc] using this

theorem oddClosure_map_toB_normal (h2 : X.coreB.index ∣ 2) :
    ((Subgroup.closure {x : C | Odd (orderOf x)}).map X.toB).Normal :=
  X.swap.oddClosure_map_toA_normal h2


theorem isPGroup_edgeA (hC : IsPGroup 2 C) : IsPGroup 2 X.edgeA :=
  hC.of_surjective X.toA.rangeRestrict X.toA.rangeRestrict_surjective

theorem isPGroup_edgeB (hC : IsPGroup 2 C) : IsPGroup 2 X.edgeB :=
  X.swap.isPGroup_edgeA hC


section Finite

variable [Finite C]

theorem isPGroup_two (hf : X.IsFaithful) (hA : X.edgeA.index = 3) (hB : X.edgeB.index = 3) :
    IsPGroup 2 C := by
  have hR : Subgroup.closure {x : C | Odd (orderOf x)} = ⊥ :=
    hf _ (X.oddClosure_map_toA_normal (X.coreA_index_dvd_two hA))
      (X.oddClosure_map_toB_normal (X.coreB_index_dvd_two hB))
  have hodd : ∀ x : C, Odd (orderOf x) → x = 1 := by
    intro x hx
    have : x ∈ Subgroup.closure {x : C | Odd (orderOf x)} := Subgroup.subset_closure hx
    rw [hR] at this
    simpa using this
  have hprime : ∀ {d : ℕ}, d.Prime → d ∣ Nat.card C → d = 2 := by
    intro d hd hdvd
    by_contra hne
    have : Fact d.Prime := ⟨hd⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' d hdvd
    have hxodd : Odd (orderOf x) := by
      rw [hx]
      exact hd.odd_of_ne_two hne
    have := hodd x hxodd
    rw [this, orderOf_one] at hx
    exact hd.one_lt.ne hx
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' hprime)


variable [Finite A]

theorem normalCore_edgeA_eq_pCore (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) : X.edgeA.normalCore = pCore 2 A := by
  have hC := X.isPGroup_two hf hA hB
  have hE : IsPGroup 2 X.edgeA := X.isPGroup_edgeA hC
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · exact le_pCore 2 (Subgroup.normalCore_normal _) (hE.to_le X.edgeA.normalCore_le)
  · have hsyl : ¬ 2 ∣ X.edgeA.index := by rw [hA]; decide
    have hN : (pCore 2 A).Normal := pCore_normal 2
    have h1 : pCore 2 A ≤ hE.toSylow hsyl := (pCore_isPGroup 2).le_sylow_of_normal _
    rw [Subgroup.normal_le_normalCore]
    exact h1

omit [Finite C] [Finite A] in
theorem coreA_index_mul_three (hA : X.edgeA.index = 3) :
    X.coreA.index * 3 = X.edgeA.normalCore.index := by
  rw [coreA_index_eq]
  have := Subgroup.relIndex_mul_index X.edgeA.normalCore_le
  rwa [hA] at this

theorem quotient_pCore_equiv (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) :
    (X.coreA.index = 1 ∧ Nonempty (A ⧸ pCore 2 A ≃* Multiplicative (ZMod 3))) ∨
    (X.coreA.index = 2 ∧ Nonempty (A ⧸ pCore 2 A ≃* Equiv.Perm (Fin 3))) := by
  have hcore := X.normalCore_edgeA_eq_pCore hf hA hB
  let q : A ⧸ pCore 2 A ≃* A ⧸ X.edgeA.normalCore := QuotientGroup.quotientMulEquivOfEq hcore.symm
  have hmul := X.coreA_index_mul_three hA
  rcases gold_normalCore_quotient_equiv hA with ⟨h3, ⟨e⟩⟩ | ⟨h6, ⟨e⟩⟩
  · exact Or.inl ⟨by omega, ⟨q.trans e⟩⟩
  · exact Or.inr ⟨by omega, ⟨q.trans e⟩⟩


end Finite

section FiniteB

variable [Finite C] [Finite B]

theorem normalCore_edgeB_eq_pCore (hf : X.IsFaithful) (hA : X.edgeA.index = 3)
    (hB : X.edgeB.index = 3) : X.edgeB.normalCore = pCore 2 B :=
  X.swap.normalCore_edgeA_eq_pCore ((X.swap_isFaithful_iff).mpr hf) hB hA


end FiniteB

section FiniteAB


end FiniteAB

section Abelian


end Abelian

section AbelianB


end AbelianB

section NormalVertex


end NormalVertex

section AbelianEdge


end AbelianEdge

end GoldAmalgam

end CFSG.Quasithin
