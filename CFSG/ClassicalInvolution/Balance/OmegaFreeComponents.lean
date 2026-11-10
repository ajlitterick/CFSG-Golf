module

public import CFSG.ClassicalInvolution.Balance.LocalBalance.Moved
public import CFSG.ClassicalInvolution.Balance.FrameIndex.Pairing

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution.Generic

variable {G : Type*} [Group G]

abbrev OddQuot (a : G) : Type _ :=
  ↥(Subgroup.centralizer ({a} : Set G)) ⧸
    componentClassificationOddCore ↥(Subgroup.centralizer ({a} : Set G))

@[expose] def oddQuotMk (a : G) : ↥(Subgroup.centralizer ({a} : Set G)) →* OddQuot a :=
  QuotientGroup.mk' (componentClassificationOddCore ↥(Subgroup.centralizer ({a} : Set G)))

@[expose] def modOdd (a : G) (K : Subgroup G) : Subgroup (OddQuot a) :=
  (K.subgroupOf (Subgroup.centralizer ({a} : Set G))).map (oddQuotMk a)

@[expose] def OmegaFreeAt (Ω : Set (Subgroup G)) (a : G) (L : Subgroup (OddQuot a)) : Prop :=
  ∀ K ∈ Ω, K ≤ Subgroup.centralizer ({a} : Set G) →
    ∀ x ∈ modOdd a K, ∀ y ∈ L, x * y = y * x

@[expose] def RankOneAt (Ω : Set (Subgroup G)) (a : G) (L : Subgroup (OddQuot a)) : Prop :=
  (∃ K ∈ Ω, K ≤ Subgroup.centralizer ({a} : Set G) ∧ modOdd a K = L) ∧
    ∀ K ∈ Ω, K ≤ Subgroup.centralizer ({a} : Set G) →
      modOdd a K = L ∨ ∀ x ∈ modOdd a K, ∀ y ∈ L, x * y = y * x

theorem mem_modOdd_iff {a : G} {K : Subgroup G} {x : OddQuot a} :
    x ∈ modOdd a K ↔ ∃ k : ↥(Subgroup.centralizer ({a} : Set G)), (k : G) ∈ K ∧ oddQuotMk a k = x :=
  Iff.rfl

theorem oddQuotMk_mem_modOdd {a : G} {K : Subgroup G} {k : G}
    (hk : k ∈ K) (hkC : k ∈ Subgroup.centralizer ({a} : Set G)) :
    oddQuotMk a ⟨k, hkC⟩ ∈ modOdd a K :=
  ⟨⟨k, hkC⟩, hk, rfl⟩

theorem oddQuotMk_eq_one_iff {a : G} {k : ↥(Subgroup.centralizer ({a} : Set G))} :
    oddQuotMk a k = 1 ↔ k ∈ componentClassificationOddCore ↥(Subgroup.centralizer ({a} : Set G)) :=
  QuotientGroup.eq_one_iff k

theorem eq_one_of_oddQuotMk_eq_one [Finite G] {a : G} {x : ↥(Subgroup.centralizer ({a} : Set G))}
    (hx : x * x = 1) (h : oddQuotMk a x = 1) : x = 1 := by
  have hmem := oddQuotMk_eq_one_iff.mp h
  have hdvd := Subgroup.orderOf_dvd_natCard _ hmem
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx)
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exfalso
    rw [h1] at hdvd
    exact (Nat.not_even_iff_odd.mpr
      (OddCore.odd_card ↥(Subgroup.centralizer ({a} : Set G)))) (even_iff_two_dvd.mpr hdvd)


section Frame

variable {F : Type*} [Field F] {Ω : Set (Subgroup G)} {E : Subgroup G} {S : Set (Subgroup G)}


theorem le_centralizer_of_mem_axisSub {a : G} {E K : Subgroup G} (h : a ∈ axisSub E K) :
    K ≤ Subgroup.centralizer ({a} : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact (mem_axisSub_iff.mp h).2 k hk


private theorem exists_two_ne_one {F₀ : Subgroup G} (h4 : Nat.card F₀ = 4) :
    ∃ x ∈ F₀, ∃ y ∈ F₀, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  have hfin : Finite F₀ := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite F₀
  have hc : 2 < Fintype.card F₀ := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp hc
  by_cases ha1 : a = 1
  · refine ⟨b, b.2, c, c.2, ?_, ?_, fun h => hbc (Subtype.ext h)⟩
    · intro h
      exact hab (ha1.trans (Subtype.ext h).symm)
    · intro h
      exact hac (ha1.trans (Subtype.ext h).symm)
  · by_cases hb1 : b = 1
    · refine ⟨a, a.2, c, c.2, fun h => ha1 (Subtype.ext h), ?_, fun h => hac (Subtype.ext h)⟩
      intro h
      exact hbc (hb1.trans (Subtype.ext h).symm)
    · by_cases hc1 : c = 1
      · exact ⟨a, a.2, b, b.2, fun h => ha1 (Subtype.ext h), fun h => hb1 (Subtype.ext h),
          fun h => hab (Subtype.ext h)⟩
      · exact ⟨a, a.2, b, b.2, fun h => ha1 (Subtype.ext h), fun h => hb1 (Subtype.ext h),
          fun h => hab (Subtype.ext h)⟩


end Frame

end CFSG.ClassicalInvolution.Balance
