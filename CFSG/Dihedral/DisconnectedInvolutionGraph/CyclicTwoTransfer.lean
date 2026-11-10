module

public import CFSG.Dihedral.DisconnectedInvolutionGraph.InvolutionGraph

public section

namespace CFSG.DisconnectedInvolutionGraph.Helpers

variable {G : Type*} [Group G] [Finite G]

theorem cyclic_involutions_unique [IsCyclic G] (first second : Involution G) :
    first = second := by
  classical
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite (Involution G)
  have hdiv : 2 ∣ Fintype.card G := by
    have hdiv := orderOf_dvd_card (x := (first : G))
    rwa [first.property] at hdiv
  have hcard : Fintype.card (Involution G) = 1 := by
    rw [Fintype.card_subtype]
    exact (IsCyclic.card_orderOf_eq_totient hdiv).trans Nat.totient_two
  have hsubsingleton : Subsingleton (Involution G) :=
    (Fintype.card_le_one_iff_subsingleton.mp (by omega))
  exact hsubsingleton.elim first second


end CFSG.DisconnectedInvolutionGraph.Helpers
