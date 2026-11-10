module

public import CFSG.ClassicalInvolution.Q3.Q3CHLift
public import CFSG.ClassicalInvolution.Q3.Q3CHModel
public import CFSG.ClassicalInvolution.Q3.Q3CPThin
public import CFSG.ClassicalInvolution.Q3.Q3NLExact

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3CH

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3.Q3CP CFSG.ClassicalInvolution.Q3.Q3NL
open scoped MatrixGroups

section Normalizer

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}


end Normalizer

section Layer

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}


theorem exists_layer_bar_comp {Xb : Type} [Group Xb] {c : CompData}
    (hc : c = CompData.model .PSp 2) (ψ : c.G →* Xb) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center c.G) {f : c.G} (hf : f ∈ Subgroup.center c.G)
    (hfz : ψ f ≠ 1) {ub : Xb} (hub : ub * ub = ψ f) :
    ∃ Lb : Subgroup Xb, Lb ≤ Subgroup.centralizer ({ub} : Set Xb) ∧
      (∀ x ∈ Subgroup.centralizer ({ub} : Set Xb), ∀ y ∈ Lb, x * y * x⁻¹ ∈ Lb) ∧
      ub * ub ∈ Lb ∧ Nonempty (Lb ≃* SL(2, ZMod 3)) := by
  subst hc
  have : Fact (Nat.card (GaloisField 3 1) = 3) :=
    ⟨by simpa using GaloisField.card 3 1 (by norm_num)⟩
  exact exists_layer_bar (F := GaloisField 3 1) ψ hψ hker hf hfz hub


end Layer

end CFSG.ClassicalInvolution.Q3.Q3CH
