module

public import CFSG.ClassicalInvolution.Balance.Theorem5Fuzzy
public import CFSG.ClassicalInvolution.Balance.BootstrapLayersFuzzyLink

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance.Theorem5
  (FuzzyFrameOn fuzzyFrames fuzzyVertices MemberClass FuzzyAxisExact card_closure_singleton_le_two)
open CFSG.Assembly.Dichotomy (involutionOddCore)
open scoped commutatorElement

section Canonical

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def canonicalMembers (p f : ℕ) [Fact p.Prime] (G : Type) [Group G] :
    Set (Subgroup G) :=
  {J | ∃ z, IsClassicalMember p f J z ∧ IsCanonical J z}


end Canonical

section Frames

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]


theorem canonMember_mem_canonicalMembers {J : Subgroup G} {z : G}
    (hJ : IsClassicalMember p f J z) : canonMember J z ∈ canonicalMembers p f G :=
  ⟨z, isClassicalMember_canonMember hJ, isCanonical_canonMember hJ.perfect⟩


theorem fuzzyFrameOn_of_axisTriangle {𝒞 : Set (Subgroup G)} {J₁ J₂ J₃ : Subgroup G}
    {z₁ z₂ z₃ : G} (hT : AxisTriangle p f J₁ J₂ J₃ z₁ z₂ z₃) (h₁ : J₁ ∈ 𝒞) (h₂ : J₂ ∈ 𝒞)
    (h₃ : J₃ ∈ 𝒞) (hne₁₂ : z₁ ≠ z₂) (hne₁₃ : z₁ ≠ z₃) (hne₂₃ : z₂ ≠ z₃) (hind : z₁ * z₂ ≠ z₃) :
    FuzzyFrameOn p f 𝒞 (triangleAxis z₁ z₂ z₃) := by
  obtain ⟨-, -, hA₁, hA₂, hA₃⟩ := hT.axis_data
  refine ⟨![J₁, J₂, J₃], ![z₁, z₂, z₃], ?_, ?_, hT.isElemAbelian,
    hT.card_axis hne₁₂ hne₁₃ hne₂₃ hind, ?_⟩
  · intro i
    fin_cases i
    exacts [⟨h₁, hT.cls₁⟩, ⟨h₂, hT.cls₂⟩, ⟨h₃, hT.cls₃⟩]
  · have hrange : Set.range ![z₁, z₂, z₃] = ({z₁, z₂, z₃} : Set G) := by
      ext x
      simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp
      · rintro (rfl | rfl | rfl)
        exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
    rw [triangleAxis, hrange]
  · intro i
    fin_cases i
    exacts [hA₁, hA₂, hA₃]


end Frames

end CFSG.ClassicalInvolution.Balance.Bootstrap
