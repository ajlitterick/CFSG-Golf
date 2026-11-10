module

public import CFSG.ClassicalInvolution.Asc77.AscC25V11
public import CFSG.ClassicalInvolution.Asc77.AscC25V3
public import CFSG.ClassicalInvolution.Asc77.AscT7TC15

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.C25V

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped MatrixGroups commutatorElement

section Defs

variable (p f : ℕ) [Fact p.Prime]


@[expose] def Fus25 : Prop :=
  p ^ f ≠ 9 → ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z t u₁ u₂ : G),
    Hyp25 p f Ω K K' W S R R' z t u₁ u₂ → ∀ a ∈ (S : Subgroup G), a * a = 1 → IsFAut R' a →
      (¬ ∃ c : G, c * a = a * c ∧ c * z = z * c ∧ conjSub c K' = K) →
        ∀ x : G, x⁻¹ * a * x ∈ Subgroup.centralizer ({z} : Set G) →
          ∃ c ∈ Subgroup.centralizer ({z} : Set G), x⁻¹ * a * x = c⁻¹ * a * c


end Defs

end CFSG.ClassicalInvolution.Asc77.C25V
