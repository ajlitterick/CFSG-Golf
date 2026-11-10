module

public import CFSG.ClassicalInvolution.Q3.Q3ABoot

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

structure IsA2Pair3 (Ω : Set (Subgroup G)) (K₁ K₂ : Subgroup G) (z₁ z₂ : G) : Prop where
  mem₁ : K₁ ∈ Ω
  mem₂ : K₂ ∈ Ω
  cls₁ : IsClassicalMember3 K₁ z₁
  cls₂ : IsClassicalMember3 K₂ z₂
  ne : z₁ ≠ z₂
  comm_involutions : z₁ * z₂ = z₂ * z₁
  not_comm : ¬ Commutes K₁ K₂

namespace IsA2Pair3

variable {Ω : Set (Subgroup G)} {K₁ K₂ : Subgroup G} {z₁ z₂ : G}

theorem symm (h : IsA2Pair3 Ω K₁ K₂ z₁ z₂) : IsA2Pair3 Ω K₂ K₁ z₂ z₁ where
  mem₁ := h.mem₂
  mem₂ := h.mem₁
  cls₁ := h.cls₂
  cls₂ := h.cls₁
  ne := h.ne.symm
  comm_involutions := h.comm_involutions.symm
  not_comm hc := h.not_comm hc.symm

end IsA2Pair3


section CommonNeighbour


end CommonNeighbour

end CFSG.ClassicalInvolution.Q3
