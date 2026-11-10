module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.ComponentAction
public import CFSG.Dihedral.DisconnectedInvolutionGraph.CrossingInvolutions

public section

open CFSG.Open

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G]

abbrev ComponentInvolutions (component : InvolutionComponent G) :=
  {involution : Involution G // involutionComponent involution = component}


noncomputable def componentInvolutionsConjugationEquiv (g : G)
    (component : InvolutionComponent G) :
    ComponentInvolutions component ≃ ComponentInvolutions (g • component) where
  toFun involution := ⟨conjugateInvolution g involution.val, by
    rw [← smul_involutionComponent, involution.property]⟩
  invFun involution := ⟨conjugateInvolution g⁻¹ involution.val, by
    rw [← smul_involutionComponent, involution.property, inv_smul_smul]⟩
  left_inv involution := by
    apply Subtype.ext
    change conjugateInvolution g⁻¹ (conjugateInvolution g involution.val) = involution.val
    rw [← conjugateInvolution_mul, inv_mul_cancel, conjugateInvolution_one]
  right_inv involution := by
    apply Subtype.ext
    change conjugateInvolution g (conjugateInvolution g⁻¹ involution.val) = involution.val
    rw [← conjugateInvolution_mul, mul_inv_cancel, conjugateInvolution_one]

theorem component_involution_card_eq [Finite G] (source target : InvolutionComponent G) :
    Nat.card (ComponentInvolutions source) = Nat.card (ComponentInvolutions target) := by
  obtain ⟨g, htransport⟩ := MulAction.exists_smul_eq G source target
  rw [← htransport]
  exact Nat.card_congr (componentInvolutionsConjugationEquiv g source)


end CFSG.DisconnectedInvolutionGraph.Helpers
