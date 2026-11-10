module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyLink

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open scoped commutatorElement

section Model

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Φ : Set (Subgroup G)} {a : G}

theorem SecData.exists_central_lift (hs : SecData p f a Φ) (D : LocalLieSystemAt p f Φ a)
    (j : Fin D.card) {K : Subgroup G} {t : G} (ht : IsCentralInvolution K t)
    (htC : t ∈ Subgroup.centralizer ({a} : Set G))
    {R : Subgroup (compModel D j).K}
    (hR : R.map (secComponentHom hs.normalizes D j) = modOdd a K) (hRp : ⁅R, R⁆ = R) :
    ∃ z ∈ R, secComponentHom hs.normalizes D j z = oddQuotMk a ⟨t, htC⟩ ∧
      ∀ r ∈ R, z * r = r * z := by
  have hmem : oddQuotMk a ⟨t, htC⟩ ∈ R.map (secComponentHom hs.normalizes D j) :=
    hR ▸ oddQuotMk_mem_modOdd ht.mem htC
  obtain ⟨z, hzR, hz⟩ := Subgroup.mem_map.mp hmem
  refine ⟨z, hzR, hz, ?_⟩
  have hcen : ∀ q ∈ R, ⁅z, q⁆ ∈ Subgroup.center (compModel D j).K := by
    intro q hq
    refine secComponentHom_ker_le_center hs.normalizes D j ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, hz]
    have hq' : secComponentHom hs.normalizes D j q ∈ modOdd a K :=
      hR ▸ Subgroup.mem_map_of_mem _ hq
    obtain ⟨k, hk, hkq⟩ := mem_modOdd_iff.mp hq'
    rw [← hkq]
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    rw [← map_mul, ← map_mul]
    exact congrArg (oddQuotMk a) (Subtype.ext (ht.central _ hk))
  exact centralizes_of_commutator_mem_center_of_perfect hRp hcen


end Model

end CFSG.ClassicalInvolution.Balance.Bootstrap
