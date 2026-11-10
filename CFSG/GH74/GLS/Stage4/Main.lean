module

public import CFSG.GH74.GLS.Stage4.Glue

public section

namespace CFSG.GH74.GLS.Stage4

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.GH74.BNPair

theorem prime_ne_two_of_odd_pow {p f q : ℕ} (hf : 1 ≤ f) (hpf : p ^ f = q) (hq : Odd q) :
    p ≠ 2 := by
  rintro rfl
  obtain ⟨k, hk⟩ := hq
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
  omega


end CFSG.GH74.GLS.Stage4
