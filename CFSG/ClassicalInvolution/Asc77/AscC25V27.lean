module

public import CFSG.ClassicalInvolution.Asc77.AscC25V25
public import CFSG.ClassicalInvolution.Asc77.AscC25V6

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

section Parity

variable {G : Type} [Group G] [Finite G]

abbrev czIn (a z : G) : Subgroup ↥(Subgroup.centralizer ({a} : Set G)) :=
  (Subgroup.centralizer ({z} : Set G)).subgroupOf (Subgroup.centralizer ({a} : Set G))

omit [Finite G] in
theorem mem_czIn {a z : G} {y : ↥(Subgroup.centralizer ({a} : Set G))} :
    y ∈ czIn a z ↔ (y : G) * z = z * (y : G) := by
  rw [czIn, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]


theorem exists_conj_comm_of_odd {a z b : G}
    (hb2 : b * b = 1) (hbY : b ∈ Subgroup.centralizer ({a} : Set G))
    (hodd : Odd (czIn a z).index) :
    ∃ d ∈ Subgroup.centralizer ({a} : Set G), (d⁻¹ * b * d) * z = z * (d⁻¹ * b * d) := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := Subgroup.centralizer ({a} : Set G) with hY
  set b' : ↥Y := ⟨b, hbY⟩ with hb'
  have hb'2 : b' * b' = 1 := Subtype.ext hb2
  have hBp : IsPGroup 2 ↥(Subgroup.zpowers b') := isPGroup_two_zpowers_of_sq hb'2
  have hndvd : ¬ 2 ∣ Nat.card (↥Y ⧸ czIn a z) := hodd.not_two_dvd_nat
  obtain ⟨x, hx⟩ := hBp.nonempty_fixed_point_of_prime_not_dvd_card (↥Y ⧸ czIn a z) hndvd
  induction x using QuotientGroup.induction_on with | _ y => ?_
  have hmem := (MulAction.mem_fixedPoints).mp hx ⟨b', Subgroup.mem_zpowers b'⟩
  have h1 : (QuotientGroup.mk ((b' : ↥Y) * y) : ↥Y ⧸ czIn a z) = QuotientGroup.mk y := hmem
  rw [QuotientGroup.eq] at h1
  have h3 := mem_czIn.mp h1
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  refine ⟨(y : G), y.2, ?_⟩
  have h3' : (y : G)⁻¹ * b⁻¹ * y * z = z * ((y : G)⁻¹ * b⁻¹ * y) := by
    simpa [mul_assoc] using h3
  rw [hbi] at h3'
  exact h3'

end Parity

section Main

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G}
  {z t u₁ u₂ t' : G}


omit [IsSimpleGroup G] in
theorem exists_order_four_of_isFAut {R' : Subgroup G} {a : G} (hF : IsFAut R' a) :
    ∃ y₀ ∈ R', orderOf y₀ = 4 ∧ y₀ * a = a * y₀ := by
  obtain ⟨-, -, Q, -, hQ, hQuat, -, -⟩ := hF
  obtain ⟨k, hk, ⟨eQ⟩⟩ := hQuat
  have : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
  refine ⟨((eQ.symm (QuaternionGroup.xa 0) : Q) : G), (hQ.1 (eQ.symm _).2).1, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact QuaternionGroup.orderOf_xa 0
  · exact Subgroup.mem_centralizer_singleton_iff.mp (hQ.1 (eQ.symm _).2).2


end Main

end CFSG.ClassicalInvolution.Asc77.C25V
