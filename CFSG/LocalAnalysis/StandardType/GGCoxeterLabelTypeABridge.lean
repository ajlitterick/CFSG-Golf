module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeAAssembly

public section

namespace CFSG.StandardType

open Module CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent


section GG

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}


theorem ggAutomizer_apply_eq_of_le_centralizer {H : Subgroup G} {x : ↥Bs}
    (hH : H ≤ Subgroup.centralizer ({(x : G)} : Set G)) {φ : MulAut ↥Bs}
    (hφ : φ ∈ ggAutomizer H Bs) : φ x = x := by
  refine Subgroup.closure_induction (p := fun ψ _ => ψ x = x) ?_ ?_ ?_ ?_ hφ
  · rintro ψ ⟨g, hgH, -, hg⟩
    apply Subtype.ext
    rw [hg]
    have hc := Subgroup.mem_centralizer_iff.mp (hH hgH) (x : G) (Set.mem_singleton _)
    rw [← hc]
    group
  · rfl
  · intro ψ χ _ _ h1 h2
    rw [MulAut.mul_apply, h2, h1]
  · intro ψ _ h
    calc ψ⁻¹ x = ψ⁻¹ (ψ x) := by rw [h]
      _ = x := MulAut.inv_apply_self _ _ _

end GG


end CFSG.StandardType
