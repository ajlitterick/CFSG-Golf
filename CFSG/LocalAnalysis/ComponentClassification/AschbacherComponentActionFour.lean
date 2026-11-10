module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherComponentActionFourNormalized

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherComponentAction

open CFSG.Open
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem rightComponent_one (L : Subgroup G) : rightComponent L 1 = L := by
  simp only [rightComponent, inv_one, UniversalOrbitBlock.conjugate_one]

theorem commuting_involution_cancel (u v : G) (hu : u * u = 1)
    (hcommute : Commute u v) : (u * v) * u = v := by
  calc
    (u * v) * u = v * (u * u) := by rw [hcommute.eq]; group
    _ = v := by rw [hu, mul_one]

theorem partner_moved_by_commuting_involution (L : Subgroup G) (u v : G)
    (hu : u * u = 1) (hcommute : Commute u v)
    (hmoved : rightComponent L v ≠ L) :
    rightComponent (rightComponent L u) v ≠ rightComponent L u := by
  intro hfixed
  have hmap := congrArg (fun M : Subgroup G => rightComponent M u) hfixed
  simp only [rightComponent_mul, commuting_involution_cancel u v hu hcommute,
    hu, rightComponent_one] at hmap
  exact hmoved hmap


variable [Finite G]

theorem moved_component_conjugate_commutes (L : Subgroup G) (u : G)
    (hL : IsComponentOf L ⊤) (hu : u * u = 1)
    (hmoved : rightComponent L u ≠ L) (x : G) (hx : x ∈ L) :
    Commute x (MulAut.conj u x) := by
  have hpartner : MulAut.conj u x ∈ rightComponent L u := by
    rw [rightComponent_involution L u hu]
    exact Subgroup.mem_map_of_mem (MulAut.conj u).toMonoidHom hx
  exact (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (moved_component_commutes L u hL hmoved) hx) _ hpartner).symm


end CFSG.ComponentClassification.AschbacherComponentAction
