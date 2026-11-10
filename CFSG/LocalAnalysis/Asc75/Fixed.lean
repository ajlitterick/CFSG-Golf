module

public import CFSG.LocalAnalysis.Asc75.Basic

public section

namespace CFSG.Asc75

open CFSG CFSG.Open

variable {G : Type*} [Group G]

@[expose] def FixedOnly (H X : Subgroup G) : Prop :=
  X ≤ H ∧ ∀ g : G, conjugate X g ≤ H → g ∈ H


theorem FixedOnly.le {H X : Subgroup G} (h : FixedOnly H X) : X ≤ H := h.1

theorem FixedOnly.mono {H X X' : Subgroup G} (h : FixedOnly H X') (hX' : X' ≤ X) (hXH : X ≤ H) :
    FixedOnly H X :=
  ⟨hXH, fun g hg => h.2 g ((conjugate_mono hX' g).trans hg)⟩

@[expose] def FixedOnlyElt (H : Subgroup G) (a : G) : Prop :=
  a ∈ H ∧ ∀ g : G, g⁻¹ * a * g ∈ H → g ∈ H


end CFSG.Asc75
