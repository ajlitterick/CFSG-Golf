module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerProducts

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u

@[expose] def SignalizerPrimeCompatible {G : Type u} [Group G]
    (prime subgroupPrime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (subgroup : Subgroup G) : Prop :=
  SignalizerCompatible prime actor signalizer subgroup ∧ IsPGroup subgroupPrime subgroup

@[expose] def CommonFixedConjugate {G : Type u} [Group G]
    (actor : Subgroup G) (signalizer : G → Subgroup G) (first second : Subgroup G) : Prop :=
  ∃ conjugator ∈ signalizerCommonFixed actor signalizer,
    first.map (MulAut.conj conjugator).toMonoidHom = second

theorem subgroup_map_conj_one {G : Type u} [Group G] (subgroup : Subgroup G) :
    subgroup.map (MulAut.conj (1 : G)).toMonoidHom = subgroup := by
  have hone : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext element
    simp
  rw [hone, Subgroup.map_id]

theorem subgroup_map_conj_inv_cancel {G : Type u} [Group G]
    (subgroup : Subgroup G) (conjugator : G) :
    (subgroup.map (MulAut.conj conjugator).toMonoidHom).map
      (MulAut.conj conjugator⁻¹).toMonoidHom = subgroup := by
  rw [← subgroup_map_conj_mul, inv_mul_cancel, subgroup_map_conj_one]

theorem CommonFixedConjugate.refl {G : Type u} [Group G]
    (actor : Subgroup G) (signalizer : G → Subgroup G) (subgroup : Subgroup G) :
    CommonFixedConjugate actor signalizer subgroup subgroup :=
  ⟨1, (signalizerCommonFixed actor signalizer).one_mem, subgroup_map_conj_one subgroup⟩

theorem CommonFixedConjugate.symm {G : Type u} [Group G]
    (actor : Subgroup G) (signalizer : G → Subgroup G) (first second : Subgroup G)
    (hconjugate : CommonFixedConjugate actor signalizer first second) :
    CommonFixedConjugate actor signalizer second first := by
  obtain ⟨conjugator, hmem, heq⟩ := hconjugate
  refine ⟨conjugator⁻¹, (signalizerCommonFixed actor signalizer).inv_mem hmem, ?_⟩
  rw [← heq, subgroup_map_conj_inv_cancel]

theorem CommonFixedConjugate.trans {G : Type u} [Group G]
    (actor : Subgroup G) (signalizer : G → Subgroup G) (first second third : Subgroup G)
    (hfirst : CommonFixedConjugate actor signalizer first second)
    (hsecond : CommonFixedConjugate actor signalizer second third) :
    CommonFixedConjugate actor signalizer first third := by
  obtain ⟨firstConjugator, hfirstMem, hfirstEq⟩ := hfirst
  obtain ⟨secondConjugator, hsecondMem, hsecondEq⟩ := hsecond
  refine ⟨secondConjugator * firstConjugator,
    (signalizerCommonFixed actor signalizer).mul_mem hsecondMem hfirstMem, ?_⟩
  rw [subgroup_map_conj_mul, hfirstEq, hsecondEq]

theorem SignalizerPrimeCompatible.bot {G : Type u} [Group G]
    (prime : ℕ) (hprime : prime.Prime) (subgroupPrime : ℕ)
    (actor : Subgroup G) (signalizer : G → Subgroup G) :
    SignalizerPrimeCompatible prime subgroupPrime actor signalizer ⊥ :=
  ⟨SignalizerCompatible.bot prime hprime actor signalizer, IsPGroup.of_subsingleton _ _⟩

theorem SignalizerPrimeCompatible.of_le {G : Type u} [Group G] [Finite G]
    (prime subgroupPrime : ℕ) (actor : Subgroup G) (signalizer : G → Subgroup G)
    (subgroup smaller : Subgroup G)
    (hcompatible : SignalizerPrimeCompatible prime subgroupPrime actor signalizer subgroup)
    (hle : smaller ≤ subgroup) (hnormalized : actor ≤ Subgroup.normalizer (smaller : Set G)) :
    SignalizerPrimeCompatible prime subgroupPrime actor signalizer smaller :=
  ⟨SignalizerCompatible.of_le prime actor signalizer subgroup smaller hcompatible.1 hle hnormalized,
    hcompatible.2.to_le hle⟩


theorem subgroup_card_lt_of_lt {G : Type u} [Group G] [Finite G]
    (first second : Subgroup G) (hstrict : first < second) : Nat.card first < Nat.card second := by
  classical
  let : Fintype first := Fintype.ofFinite _
  let : Fintype second := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  apply Fintype.card_lt_of_injective_not_surjective (Subgroup.inclusion hstrict.le)
    (Subgroup.inclusion_injective hstrict.le)
  intro hsurjective
  apply hstrict.not_ge
  intro element helement
  obtain ⟨preimage, hpreimage⟩ := hsurjective ⟨element, helement⟩
  have heq : (preimage : G) = element := congrArg Subtype.val hpreimage
  exact heq ▸ preimage.property

end CFSG.RankThreeEvenClassification.Helpers
