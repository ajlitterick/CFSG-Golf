module

public import CFSG.CharacterTheory.Wreathed.OddKernelFixedSpaceCharacter
public import CFSG.Dihedral.DisconnectedInvolutionGraph.IrreducibleDegree
public import Mathlib.Order.CompletePartialOrder

public noncomputable section

namespace CFSG.Wreathed.SameFieldOddKernel

variable {G : Type*} [Group G] [IsSimpleGroup G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem representation_ker_eq_bot_of_simple (ρ : Representation ℂ G V)
    (hρ : ∃ g : G, ρ g ≠ 1) : MonoidHom.ker ρ = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker ρ) with h | h
  · exact h
  · obtain ⟨g, hg⟩ := hρ
    exact False.elim (hg (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top g)))

theorem irreducible_ker_eq_bot_of_degree_ne_one [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] (hdegree : ρ.character 1 ≠ 1) :
    MonoidHom.ker ρ = ⊥ := by
  apply representation_ker_eq_bot_of_simple ρ
  apply CFSG.DisconnectedInvolutionGraph.Helpers.irreducible_nonprincipal_action_nontrivial ρ
  intro h
  exact hdegree (congrFun h 1)

omit [IsSimpleGroup G] in
theorem subgroup_eq_bot_of_image_le_ker (ρ : Representation ℂ G V)
    (hρ : MonoidHom.ker ρ = ⊥) (K : Subgroup G) (O : Subgroup K)
    (hO : O.map K.subtype ≤ MonoidHom.ker ρ) : O = ⊥ := by
  apply le_bot_iff.mp
  intro o ho
  have hmem : (o : G) ∈ MonoidHom.ker ρ := hO ⟨o, ho, rfl⟩
  have hone : (o : G) = 1 := Subgroup.mem_bot.mp (hρ ▸ hmem)
  exact Subgroup.mem_bot.mpr (Subtype.ext hone)

section FixedSpace


end FixedSpace

end CFSG.Wreathed.SameFieldOddKernel
