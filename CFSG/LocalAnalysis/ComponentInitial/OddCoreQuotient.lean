module

public import CFSG.LocalAnalysis.ComponentInitial.OddCoreCorrespondence
public import CFSG.LocalAnalysis.LyonsUnitaryFour.CentralHall

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup

variable {G : Type*} [Group G]

theorem pPrimeCore_le_of_isPGroup_quotient [Finite G] {p : ℕ} [Fact p.Prime]
    {N : Subgroup G} [N.Normal] (hGN : IsPGroup p (G ⧸ N)) : pPrimeCore p G ≤ N := fun d hd => by
  refine mem_of_coprime_orderOf hGN ?_
  rw [← Subgroup.orderOf_mk d hd]
  exact (pPrimeCore_coprime_card (p := p) (G := G)).coprime_dvd_right (orderOf_dvd_natCard _)

theorem le_pPrimeCore {p : ℕ} {N : Subgroup G} (hN : N.Normal)
    (hcop : Nat.Coprime p (Nat.card N)) : N ≤ pPrimeCore p G :=
  le_sSup ⟨hN, hcop⟩

theorem le_pCore {p : ℕ} {N : Subgroup G} (hN : N.Normal) (hp : IsPGroup p N) :
    N ≤ pCore p G :=
  le_sSup ⟨hN, hp⟩


theorem pCore_normal_intersection [Finite G] (p : ℕ) [Fact p.Prime] {N : Subgroup G}
    (hN : N.Normal) : (pCore p N).map N.subtype = N ⊓ pCore p G := by
  have := CFSG.LocalCores.prime_set_core_normal_intersection {q : Nat.Primes | q.val = p} hN
  rwa [← CFSG.pCore_eq_piCore, ← CFSG.pCore_eq_piCore] at this

theorem mem_pPrimeCore_of_mem_center {p : ℕ} {z : G} (hz : z ∈ center G)
    (hcop : Nat.Coprime p (orderOf z)) : z ∈ pPrimeCore p G := by
  refine le_pPrimeCore (normal_of_le_center ((zpowers_le).2 hz)) ?_ (mem_zpowers z)
  rwa [Nat.card_zpowers]

theorem coprime_orderOf_of_mem_pPrimeCore [Finite G] {p : ℕ} [Fact p.Prime] {z : G}
    (hz : z ∈ pPrimeCore p G) : Nat.Coprime p (orderOf z) := by
  rw [← Subgroup.orderOf_mk z hz]
  exact (pPrimeCore_coprime_card (p := p) (G := G)).coprime_dvd_right (orderOf_dvd_natCard _)

section Correspondence

variable {B C : Type*} [Group B] [Group C] {I : Subgroup C}


variable {f : B →* I}

theorem map_pPrimeCore_le [Finite B] (hf : Function.Surjective f) :
    (pPrimeCore 2 B).map f ≤ pPrimeCore 2 I := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pPrimeCore ((pPrimeCore_normal (p := 2) (G := B)).map f hf)
    ((pPrimeCore_coprime_card (p := 2) (G := B)).coprime_dvd_right (Subgroup.card_map_dvd _ _))


end Correspondence


end CFSG.LocalAnalysis.ComponentInitial
