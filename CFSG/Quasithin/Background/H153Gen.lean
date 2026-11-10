module

public import CFSG.Quasithin.Background.H156Gen
public import CFSG.Quasithin.Background.H153Defs

public section

namespace CFSG.Quasithin.H153

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H156

section Transport

variable {V W : Type*} [CommGroup V] [CommGroup W]


end Transport

section Pairing

variable {V : Type*} [CommGroup V]


theorem eq_one_or_of_mem_zpowers {z c : V} (hz : z * z = 1) (hc : c ∈ Subgroup.zpowers z) :
    c = 1 ∨ c = z := by
  obtain ⟨k, rfl⟩ := hc
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, hz]
  change z ^ k = 1 ∨ z ^ k = z
  rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, h2, one_zpow, mul_one]
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> rw [h] <;> simp


end Pairing

end CFSG.Quasithin.H153
