module

public import CFSG.ClassicalInvolution.AschTight.S1916Local

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] [Finite G] {K : Subgroup G} {z : G}

omit [Finite G] in
theorem normalizer_le_centralizer_of_isUniqueInvolution {M : Subgroup G}
    (hz : IsUniqueInvolution M z) :
    Subgroup.normalizer (M : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
  intro n hn
  have h1 : n * z * n⁻¹ = z := hz.conj_eq (mem_normalizer_iff_conjSub_eq.mp hn)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * z = n * z * n⁻¹ * n := by group
    _ = z * n := by rw [h1]


end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
