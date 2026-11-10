module

public import CFSG.ClassicalInvolution.Q3.Q3ARank
public import CFSG.ClassicalInvolution.Balance.GoodDataBasic

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

section Vocabulary

variable {G : Type} [Group G]

@[expose] def nbrs3 (Ω : Set (Subgroup G)) (K : Subgroup G) : Set (Subgroup G) :=
  {J | J ∈ Ω ∧ J ≠ K ∧ Commutes K J}

@[expose] def nbrSpan3 (Ω : Set (Subgroup G)) (K : Subgroup G) : Subgroup G :=
  ⨆ J ∈ nbrs3 Ω K, J

variable {Ω : Set (Subgroup G)} {K J : Subgroup G}


theorem le_nbrSpan3 (h : J ∈ nbrs3 Ω K) : J ≤ nbrSpan3 Ω K :=
  le_iSup₂ (f := fun (J : Subgroup G) (_ : J ∈ nbrs3 Ω K) => J) J h


theorem conjSub_eq_self_of_mem_centralizer {x : G} (hx : x ∈ Subgroup.centralizer (K : Set G)) :
    conjSub x K = K := by
  have hc : ∀ k ∈ K, k * x = x * k := fun k hk => Subgroup.mem_centralizer_iff.mp hx k hk
  ext y
  rw [mem_conjSub_iff]
  constructor
  · intro hy
    have h1 : (x⁻¹ * y * x) * x = y * x := by
      rw [hc _ hy]
      group
    have h2 : x⁻¹ * y * x = y := mul_right_cancel h1
    rwa [h2] at hy
  · intro hy
    have h1 : x⁻¹ * y * x = y := by
      have : y * x = x * y := hc y hy
      calc x⁻¹ * y * x = x⁻¹ * (y * x) := by rw [mul_assoc]
        _ = x⁻¹ * (x * y) := by rw [this]
        _ = y := by rw [← mul_assoc, inv_mul_cancel, one_mul]
    rwa [h1]


end Vocabulary

section Class


end Class

section FourGroups


end FourGroups

section NoA2


end NoA2


end CFSG.ClassicalInvolution.Q3
