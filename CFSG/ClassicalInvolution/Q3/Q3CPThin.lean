module

public import CFSG.ClassicalInvolution.Q3.Q3CPLocC
public import CFSG.ClassicalInvolution.AschTight.Hall196Idx
public import CFSG.ClassicalInvolution.Q3.Q3CPNotThin

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CP

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Asc77

section Generic

variable {G : Type} [Group G] [Finite G]


end Generic

section Thin

variable {G : Type} [Group G] [Finite G]

structure ThinData (Ω : Set (Subgroup G)) (K₁ K₂ : Subgroup G) (z₁ z₂ : G) : Prop where
  edge : IsEdge3 Ω K₁ K₂ z₁ z₂
  thin : nbrSpan3 Ω K₁ ≤ K₂ ⊔ Balance.oddCoreIn (nbrSpan3 Ω K₁)
  congr : ∀ x ∈ nbrSpan3 Ω K₁, ∀ y ∈ nbrSpan3 Ω K₁, x * x = 1 → y * y = 1 → x ≠ 1 → y ≠ 1 →
    x * y⁻¹ ∈ Balance.oddCoreIn (nbrSpan3 Ω K₁)

namespace ThinData

variable {Ω : Set (Subgroup G)} {K₁ K₂ : Subgroup G} {z₁ z₂ : G}

theorem mem_nbrs (h : ThinData Ω K₁ K₂ z₁ z₂) : K₂ ∈ nbrs3 Ω K₁ :=
  ⟨h.edge.mem₂, fun hh => h.edge.ne (involution_unique3 h.edge.cls₁ (hh ▸ h.edge.cls₂)),
    h.edge.comm⟩

theorem le_nbrSpan (h : ThinData Ω K₁ K₂ z₁ z₂) : K₂ ≤ nbrSpan3 Ω K₁ := le_nbrSpan3 h.mem_nbrs

theorem z₂_mem (h : ThinData Ω K₁ K₂ z₁ z₂) : z₂ ∈ nbrSpan3 Ω K₁ :=
  h.le_nbrSpan h.edge.cls₂.mem


theorem eq_of_comm (h : ThinData Ω K₁ K₂ z₁ z₂) {x : G} (hx : x ∈ nbrSpan3 Ω K₁)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hc : x * z₂ = z₂ * x) : x = z₂ := by
  have hz2sq : z₂ * z₂ = 1 := h.edge.cls₂.isCentralInvolution.sq
  have h1 := h.congr x hx z₂ h.z₂_mem hx2 hz2sq hx1 h.edge.cls₂.ne_one
  have hz2inv : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right hz2sq
  rw [hz2inv] at h1
  have hsq : (x * z₂) * (x * z₂) = 1 := by
    calc (x * z₂) * (x * z₂) = x * (z₂ * x) * z₂ := by group
      _ = x * (x * z₂) * z₂ := by rw [← hc]
      _ = (x * x) * (z₂ * z₂) := by group
      _ = 1 := by rw [hx2, hz2sq, one_mul]
  have h2 : x * z₂ = 1 := eq_one_of_mem_of_odd_of_sq (Balance.odd_card_oddCoreIn _) h1 hsq
  calc x = x * z₂ * z₂⁻¹ := by group
    _ = z₂⁻¹ := by rw [h2, one_mul]
    _ = z₂ := hz2inv

end ThinData

end Thin

section Branch


end Branch

end CFSG.ClassicalInvolution.Q3.Q3CP
