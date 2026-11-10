module

public import CFSG.ClassicalInvolution.Asc77.AscT7BHyp23
public import CFSG.ClassicalInvolution.Asc77.AscT7BThmE

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable (p f : ℕ) [Fact p.Prime]


variable {p f}

theorem gamma2_le_normalizer_alphaOf {G : Type} [Group G] {B α₀ : Subgroup G}
    (h : ∀ A : Subgroup G, A ≤ B → IsElemAbelian2 A 2 → alphaOf A = α₀) (H : Subgroup G) :
    gamma2 B H ≤ Subgroup.normalizer (α₀ : Set G) := by
  refine iSup₂_le fun A hA => ?_
  have hA' : A ≤ B ∧ IsElemAbelian2 A 2 := hA
  calc H ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (A : Set G) := inf_le_right
    _ ≤ Subgroup.normalizer (alphaOf A : Set G) := T7B.centralizer_le_normalizer_alphaOf A
    _ = Subgroup.normalizer (α₀ : Set G) := by rw [h A hA'.1 hA'.2]


end CFSG.ClassicalInvolution.Asc77
