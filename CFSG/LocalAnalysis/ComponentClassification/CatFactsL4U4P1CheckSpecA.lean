module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4P1Check
public import CFSG.Sporadic.SmallOddCore.CentSpec
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Cent

public section

namespace CFSG.ComponentClassification.HarrisLit.P1

open CFSG Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier

variable {n : ℕ}


section Index

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem relIndex_mul_card_of_le {C K : Subgroup G} (hKC : K ≤ C) :
    K.relIndex C * Nat.card K = Nat.card C := by
  rw [← card_mul_index (K.subgroupOf C), Nat.card_congr (subgroupOfEquivOfLe hKC).toEquiv,
    mul_comm, relIndex]

omit [Finite G] in
theorem mem_of_coprime_relIndex {C K : Subgroup G} (hKC : K ≤ C)
    (hN : C ≤ normalizer (K : Set G)) {g : G} (hg : g ∈ C)
    (hcop : Nat.Coprime (orderOf g) (K.relIndex C)) : g ∈ K := by
  have hnorm : (K.subgroupOf C).Normal := (normal_subgroupOf_iff_le_normalizer hKC).mpr hN
  set x : ↥C := ⟨g, hg⟩
  have h1 : orderOf (QuotientGroup.mk x : ↥C ⧸ K.subgroupOf C) ∣ orderOf g := by
    rw [← Subgroup.orderOf_mk g hg]
    exact orderOf_map_dvd (QuotientGroup.mk' (K.subgroupOf C)) x
  have h2 : orderOf (QuotientGroup.mk x : ↥C ⧸ K.subgroupOf C) ∣ K.relIndex C := by
    rw [relIndex, index]
    exact orderOf_dvd_natCard _
  have h4 := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.dvd_one, orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4
  exact h4

omit [Finite G] in
theorem oddPart_le_of_relIndex {C K : Subgroup G} (hKC : K ≤ C)
    (hN : C ≤ normalizer (K : Set G)) {a : ℕ} (ha : K.relIndex C = 2 ^ a) :
    Q81.oddPart C ≤ K := by
  rw [Q81.oddPart, closure_le]
  rintro g ⟨hgC, hodd⟩
  refine mem_of_coprime_relIndex hKC hN hgC ?_
  rw [ha]
  exact Nat.Coprime.pow_right a (Odd.coprime_two_right hodd)

omit [Finite G] in
theorem closure_le_oddPart {C : Subgroup G} {S : Set G}
    (hS : ∀ x ∈ S, x ∈ C ∧ Odd (orderOf x)) : closure S ≤ Q81.oddPart C := by
  rw [closure_le]
  intro x hx
  exact Q81.mem_oddPart (hS x hx).1 (hS x hx).2

end Index

end CFSG.ComponentClassification.HarrisLit.P1
