
module

public import CFSG.Monster.B.TwoA.Base.PetersenCBase

public import CFSG.Monster.B.TwoA.Base.PetersenA

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.Lifts CFSG.Monster.VisCert CFSG.Sporadic.Mathieu

open scoped Pointwise

theorem pairSpace_UR4
    (c : Fin 15) : PairSpace (UR4 c) (R4 c) := by
  have h := pairSpace_U3.map_monomial (kmon (aut4 c) (aut4_mem_Ppair c)).2
  rwa [show aut4 c • A2 = R4 c from perm4_smul_A2 c] at h

theorem pairSpace_UR5
    (d : Fin 10) : PairSpace (UR5 d) (R5 d) := by
  have h := pairSpace_U4.map_monomial (kmon (aut5 d) (aut5_mem_Ppair d)).2
  rwa [show aut5 d • A3 = R5 d from perm5_smul_A3 d] at h

theorem Y4_eq_conjSub
    (c : Fin 15) : ∃ g ∈ K3, conjSub g E4 = Y4 c := by
  obtain ⟨g, hg, hgU⟩ := exists_K3_conjSub_EU (aut4_mem_Ppair c) (perm4_fix c 2 (by decide))
    (perm4_fix c 3 (by decide))
  exact ⟨g, hg, by rw [E4_eq_EU, hgU]; rfl⟩

theorem Y5_eq_conjSub
    (d : Fin 10) : ∃ g ∈ K3, conjSub g E5 = Y5 d := by
  obtain ⟨g, hg, hgU⟩ := exists_K3_conjSub_EU (aut5_mem_Ppair d) (perm5_fix d 2 (by decide))
    (perm5_fix d 3 (by decide))
  exact ⟨g, hg, by rw [E5_eq_EU, hgU]; rfl⟩

theorem Y4_mem_X4
    (c : Fin 15) : Y4 c ∈ X4 := by
  rw [X4_eq]
  obtain ⟨g, hg, h⟩ := Y4_eq_conjSub c
  exact ⟨g, hg, h.symm⟩

theorem Y5_mem_X5
    (d : Fin 10) : Y5 d ∈ X5 := by
  rw [X5_eq]
  obtain ⟨g, hg, h⟩ := Y5_eq_conjSub d
  exact ⟨g, hg, h.symm⟩


theorem Y4_injective :
    Function.Injective Y4 := by
  intro c c' h
  have h1 : UR4 c = UR4 c' := le_antisymm (EU_le_EU_iff.1 h.le) (EU_le_EU_iff.1 h.ge)
  exact R4_injective (Finset.Subset.antisymm
    (((pairSpace_UR4 c).le_iff (pairSpace_UR4 c')).1 h1.le)
    (((pairSpace_UR4 c').le_iff (pairSpace_UR4 c)).1 h1.ge))

theorem Y5_injective :
    Function.Injective Y5 := by
  intro d d' h
  have h1 : UR5 d = UR5 d' := le_antisymm (EU_le_EU_iff.1 h.le) (EU_le_EU_iff.1 h.ge)
  exact R5_injective (Finset.Subset.antisymm
    (((pairSpace_UR5 d).le_iff (pairSpace_UR5 d')).1 h1.le)
    (((pairSpace_UR5 d').le_iff (pairSpace_UR5 d)).1 h1.ge))

instance finite_X4 :
    Finite X4 := Nat.finite_of_card_ne_zero (by rw [natCard_X4]; decide)

instance finite_X5 :
    Finite X5 := Nat.finite_of_card_ne_zero (by rw [natCard_X5]; decide)

@[expose] def enum4 :
    Fin 15 ≃ X4 :=
  Equiv.ofBijective (fun c => ⟨Y4 c, Y4_mem_X4 c⟩)
    (Function.Injective.bijective_of_nat_card_le
      (fun c c' h => Y4_injective (congrArg Subtype.val h)) (by rw [natCard_X4, Nat.card_fin]))

@[expose] def enum5 :
    Fin 10 ≃ X5 :=
  Equiv.ofBijective (fun d => ⟨Y5 d, Y5_mem_X5 d⟩)
    (Function.Injective.bijective_of_nat_card_le
      (fun d d' h => Y5_injective (congrArg Subtype.val h)) (by rw [natCard_X5, Nat.card_fin]))


end CFSG.Monster.B.TwoA
