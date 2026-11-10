module

public import CFSG.ClassicalInvolution.Q3.Q3PBranch
public import CFSG.ClassicalInvolution.Q3.Generation

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

structure IsEdge3 (Ω : Set (Subgroup G)) (K₁ K₂ : Subgroup G) (z₁ z₂ : G) : Prop where
  mem₁ : K₁ ∈ Ω
  mem₂ : K₂ ∈ Ω
  cls₁ : IsClassicalMember3 K₁ z₁
  cls₂ : IsClassicalMember3 K₂ z₂
  comm : Commutes K₁ K₂
  ne : z₁ ≠ z₂

namespace IsEdge3

variable {Ω : Set (Subgroup G)} {K₁ K₂ : Subgroup G} {z₁ z₂ : G}

theorem comm_involutions (h : IsEdge3 Ω K₁ K₂ z₁ z₂) : z₁ * z₂ = z₂ * z₁ :=
  h.comm z₁ h.cls₁.mem z₂ h.cls₂.mem


theorem le_centralizer_pair (h : IsEdge3 Ω K₁ K₂ z₁ z₂) :
    K₁ ≤ Subgroup.centralizer (Subgroup.closure ({z₁, z₂} : Set G) : Set G) := by
  rw [Subgroup.centralizer_closure]
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rcases hx with rfl | hx
  · exact (Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le h.cls₁.subnormal hk)).symm
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact (h.comm k hk _ h.cls₂.mem).symm

theorem symm (h : IsEdge3 Ω K₁ K₂ z₁ z₂) : IsEdge3 Ω K₂ K₁ z₂ z₁ where
  mem₁ := h.mem₂
  mem₂ := h.mem₁
  cls₁ := h.cls₂
  cls₂ := h.cls₁
  comm x hx y hy := (h.comm y hy x hx).symm
  ne := h.ne.symm

theorem le_centralizer_pair' (h : IsEdge3 Ω K₁ K₂ z₁ z₂) :
    K₂ ≤ Subgroup.centralizer (Subgroup.closure ({z₁, z₂} : Set G) : Set G) := by
  have := h.symm.le_centralizer_pair
  rwa [Set.pair_comm] at this

end IsEdge3

section Class

variable [Finite G] {K : Subgroup G} {z : G}

theorem conjClass3_involution (hz : IsClassicalMember3 K z) {L : Subgroup G} {w : G}
    (hL : L ∈ conjClass3 K) (hw : IsClassicalMember3 L w) :
    ∃ g : G, L = conjSub g K ∧ w = g * z * g⁻¹ := by
  obtain ⟨g, rfl⟩ := hL
  exact ⟨g, rfl, involution_unique3 hw (hz.conj g)⟩

theorem commutes_of_not_a2Configuration3 (hz : IsClassicalMember3 K z)
    (hA2 : ¬ A2Configuration z K) {L M : Subgroup G} {a b : G} (hL : L ∈ conjClass3 K)
    (hM : M ∈ conjClass3 K) (ha : IsClassicalMember3 L a) (hb : IsClassicalMember3 M b)
    (hab : a ≠ b) (hc : a * b = b * a) : Commutes L M := by
  obtain ⟨g, rfl, rfl⟩ := conjClass3_involution hz hL ha
  obtain ⟨h, rfl, rfl⟩ := conjClass3_involution hz hM hb
  by_contra hn
  apply hA2
  refine ⟨g⁻¹, h⁻¹, ?_, ?_, ?_, ?_⟩
  · intro heq
    apply hab
    have hz1 := hz.conj g
    have hz2 : IsClassicalMember3 (conjSub g K) (h * z * h⁻¹) := by
      have : conjSub g K = conjSub h K := by simpa [conjSub] using heq
      rw [this]
      exact hz.conj h
    exact involution_unique3 hz1 hz2
  · simpa using hab
  · simpa using hc
  · simpa [conjSub] using hn


end Class

end CFSG.ClassicalInvolution.Q3
