module

public import CFSG.Mathlib.GroupTheory.Basic
public import CFSG.Foundations.KCoreOpen

public section

open CFSG.Open

namespace CFSG.ComponentClassification.Helpers

theorem not_isMulCommutative (G : Type*) [Group G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative G := by
  rintro hcomm
  obtain ⟨left, right, hne⟩ := hnonab
  exact hne ((isMulCommutative_iff.mp hcomm) left right)

theorem center_eq_bot (G : Type*) [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases CFSG.eq_bot_or_eq_top_of_normal (Subgroup.center G)
      (inferInstance : (Subgroup.center G).Normal) with hbot | htop
  · exact hbot
  · exact (not_isMulCommutative G hnonab
      (Subgroup.center_eq_top_iff.mp htop)).elim

theorem commutator_eq_top (G : Type*) [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) : commutator G = ⊤ := by
  rcases CFSG.eq_bot_or_eq_top_of_normal (commutator G)
      (inferInstance : (commutator G).Normal) with hbot | htop
  · exact (not_isMulCommutative G hnonab
      ((commutator_eq_bot_iff G).mp hbot)).elim
  · exact htop

theorem centralizer_ne_top_of_involution (G : Type*) [Group G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (involution : G)
    (hinvolution : orderOf involution = 2) :
    Subgroup.centralizer ({involution} : Set G) ≠ ⊤ := by
  intro htop
  have hcenter : involution ∈ Subgroup.center G := by
    apply Subgroup.mem_center_iff.mpr
    intro element
    have hmem : element ∈ Subgroup.centralizer ({involution} : Set G) := by
      rw [htop]
      exact Subgroup.mem_top element
    exact (Subgroup.mem_centralizer_iff.mp hmem involution (by simp)).symm
  rw [center_eq_bot G hnonab] at hcenter
  have hone : involution = 1 := Subgroup.mem_bot.mp hcenter
  simp [hone] at hinvolution

theorem even_card_of_involution (G : Type*) [Group G] (involution : G)
    (hinvolution : orderOf involution = 2) : Even (Nat.card G) := by
  apply even_iff_two_dvd.mpr
  simpa [hinvolution] using orderOf_dvd_natCard involution

theorem oddCore_eq_bot_of_involution (G : Type*) [Group G] [IsSimpleGroup G]
    (involution : G) (hinvolution : orderOf involution = 2) :
    componentClassificationOddCore G = ⊥ := by
  apply le_antisymm _ bot_le
  apply sSup_le
  intro subgroup hsubgroup
  rcases CFSG.eq_bot_or_eq_top_of_normal subgroup hsubgroup.1 with hbot | htop
  · exact hbot.le
  · have hodd : Odd (Nat.card G) := by
      simpa [htop] using hsubgroup.2
    have hdiv : 2 ∣ Nat.card G := by
      simpa [hinvolution] using orderOf_dvd_natCard involution
    exact (hodd.not_two_dvd_nat hdiv).elim

theorem oddCore_eq_bot_of_componentType (G : Type*) [Group G] [IsSimpleGroup G]
    (hcomp : componentClassificationComponentType G) :
    componentClassificationOddCore G = ⊥ := by
  obtain ⟨involution, hinvolution, _⟩ := hcomp
  exact oddCore_eq_bot_of_involution G involution hinvolution

theorem nonabelian_of_equiv {G H : Type*} [Group G] [Group H] (equivalence : G ≃* H)
    (hnonab : ∃ a b : H, a * b ≠ b * a) : ∃ a b : G, a * b ≠ b * a :=
  CFSG.KCore.nonabelian_of_mulEquiv equivalence hnonab

theorem simple_quotient_order_of_surjective (G : Type*) [Group G]
    (hK : IsKProperByOrder G) (subgroup : Subgroup G) (hproper : subgroup ≠ ⊤)
    (simple : Type*) [Group simple] [IsSimpleGroup simple]
    (hnonab : ∃ a b : simple, a * b ≠ b * a)
    (quotient : subgroup →* simple) (hsurjective : Function.Surjective quotient) :
    Nat.card simple ∈ knownSimpleOrders :=
  CFSG.KCore.KProperNonab.catalogue_of_surjective_transfer CFSG.Open.knownSimpleOrders_isoTransfer hK
    subgroup hproper hnonab quotient hsurjective


theorem quasisimple_central_quotient_nonabelian (G : Type*) [Group G]
    (hquasisimple : IsQuasisimple G) :
    ∃ a b : G ⧸ Subgroup.center G, a * b ≠ b * a := by
  let : Group.IsPerfect G := ⟨hquasisimple.1⟩
  let : IsSimpleGroup (G ⧸ Subgroup.center G) := hquasisimple.2
  have hnoncomm := Group.IsPerfect.not_isMulCommutative (G ⧸ Subgroup.center G)
  simpa only [isMulCommutative_iff, not_forall] using hnoncomm


theorem twoRank_witness (G : Type*) [Group G] [Finite G] :
    ∃ elementary : Subgroup G,
      IsElemAbelian 2 elementary ∧ Nat.card elementary = 2 ^ twoRank G := by
  have hnonempty : {rank | ∃ elementary : Subgroup G,
      elementary ≤ ⊤ ∧ IsElemAbelian 2 elementary ∧ Nat.card elementary = 2 ^ rank}.Nonempty := by
    refine ⟨0, ⊥, bot_le, ?_, ?_⟩
    · constructor
      · infer_instance
      · intro element hmem
        simp only [Subgroup.mem_bot] at hmem
        simp [hmem]
    · simp
  have hbounded : BddAbove {rank | ∃ elementary : Subgroup G,
      elementary ≤ ⊤ ∧ IsElemAbelian 2 elementary ∧ Nat.card elementary = 2 ^ rank} := by
    refine ⟨Nat.card G, ?_⟩
    rintro rank ⟨elementary, _, _, hcard⟩
    have hle := elementary.card_le_card_group
    rw [hcard] at hle
    exact (Nat.lt_two_pow_self (n := rank)).le.trans hle
  obtain ⟨elementary, _, helementary, hcard⟩ := Nat.sSup_mem hnonempty hbounded
  exact ⟨elementary, helementary, hcard⟩


end CFSG.ComponentClassification.Helpers
