module

public import CFSG.GroupTheory.PRankCoprimeQuotient
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.Foundations.Catalog

public section

namespace CFSG.LocalAnalysis

open Subgroup

namespace SQTKTwoCoreQuotient


theorem not_dvd_card_pCore_two {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) : ¬ p ∣ Nat.card (pCore 2 H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 2) (G := H))
  rw [hk]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))

end SQTKTwoCoreQuotient


end CFSG.LocalAnalysis
