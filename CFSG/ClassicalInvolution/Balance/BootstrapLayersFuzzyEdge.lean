module

public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyCanon

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.Assembly.Dichotomy (involutionOddCore)
open CFSG.RankThreeCoreUniqueness.Helpers (perfectResidualOf)
open scoped commutatorElement

section Edge

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]


end Edge

section Twins

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

omit [Fact p.Prime] in
theorem le_sup_involutionOddCore_of_modOdd_le {J J' : Subgroup G} {z : G}
    (hJ : J ≤ Subgroup.centralizer ({z} : Set G)) (h : modOdd z J ≤ modOdd z J') :
    J ≤ J' ⊔ involutionOddCore z := by
  intro x hx
  have hxC : x ∈ Subgroup.centralizer ({z} : Set G) := hJ hx
  obtain ⟨k, hk, hkx⟩ := mem_modOdd_iff.mp (h (oddQuotMk_mem_modOdd hx hxC))
  have h1 : oddQuotMk z (k⁻¹ * ⟨x, hxC⟩) = 1 := by
    rw [map_mul, map_inv, hkx, inv_mul_cancel]
  have h2 : (k⁻¹ * ⟨x, hxC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) ∈
      componentClassificationOddCore ↥(Subgroup.centralizer ({z} : Set G)) :=
    oddQuotMk_eq_one_iff.mp h1
  have h3 : ((k⁻¹ * ⟨x, hxC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) : G) ∈
      involutionOddCore z := ⟨_, h2, rfl⟩
  have e : x = (k : G) * ((k⁻¹ * ⟨x, hxC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) : G) := by
    simp
  rw [e]
  exact Subgroup.mul_mem_sup hk h3

omit [Fact p.Prime] in
theorem sup_involutionOddCore_eq_of_modOdd_eq {J J' : Subgroup G} {z : G}
    (hJ : J ≤ Subgroup.centralizer ({z} : Set G)) (hJ' : J' ≤ Subgroup.centralizer ({z} : Set G))
    (h : modOdd z J = modOdd z J') : J ⊔ involutionOddCore z = J' ⊔ involutionOddCore z :=
  le_antisymm
    (sup_le (le_sup_involutionOddCore_of_modOdd_le hJ h.le) le_sup_right)
    (sup_le (le_sup_involutionOddCore_of_modOdd_le hJ' h.ge) le_sup_right)

variable [Finite G]

theorem canonical_twins_eq_or_nadj {J J' : Subgroup G} {z : G} (hq : 5 ≤ p ^ f)
    (hJ : IsClassicalMember p f J z) (hJ' : IsClassicalMember p f J' z) (hc : IsCanonical J z)
    (hc' : IsCanonical J' z) :
    J = J' ∨ ∀ x ∈ J, ∀ y ∈ J', ⁅x, y⁆ ∈ involutionOddCore z := by
  have hJC : J ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hJ.subnormal
  have hJ'C : J' ≤ Subgroup.centralizer ({z} : Set G) := isSubnormal_le hJ'.subnormal
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute
    ((AssemblyBPredicates.isComponentOf_iff_open _ ⊤).mpr (isComponentOf_modOdd hJ hq))
    ((AssemblyBPredicates.isComponentOf_iff_open _ ⊤).mpr (isComponentOf_modOdd hJ' hq)) with h | h
  · left
    have hsup := sup_involutionOddCore_eq_of_modOdd_eq hJC hJ'C h
    unfold IsCanonical at hc hc'
    rw [← hc, hsup, hc']
  · right
    intro x hx y hy
    rw [involutionOddCore_eq_oddCoreIn]
    have hxC := hJC hx
    have hyC := hJ'C hy
    refine (mk_comm_eq_iff (Y := Subgroup.centralizer ({z} : Set G)) hxC hyC).mp ?_
    have h1 : ⁅oddQuotMk z ⟨x, hxC⟩, oddQuotMk z ⟨y, hyC⟩⁆ ∈ ⁅modOdd z J, modOdd z J'⁆ :=
      Subgroup.commutator_mem_commutator (oddQuotMk_mem_modOdd hx hxC)
        (oddQuotMk_mem_modOdd hy hyC)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1


end Twins

end CFSG.ClassicalInvolution.Balance.Bootstrap
