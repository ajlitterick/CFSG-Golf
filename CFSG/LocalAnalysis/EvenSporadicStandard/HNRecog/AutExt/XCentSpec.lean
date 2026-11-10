module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XInnerSpec
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XCentAbs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4.XModel

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.EvenSporadicStandard.HNRecog.Section3

theorem card_cent_eq (T : ↥XP) :
    Nat.card ↥(centralizer ({T} : Set ↥XP)) =
      {g : Equiv.Perm (Fin 1408) | g ∈ XP ∧ g * (T : Equiv.Perm (Fin 1408)) = T * g}.ncard := by
  rw [← Nat.card_coe_set_eq]
  exact Nat.card_congr
    { toFun := fun x => ⟨(x.1 : Equiv.Perm (Fin 1408)), x.1.2,
        congrArg Subtype.val (mem_centralizer_singleton_iff.1 x.2)⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, mem_centralizer_singleton_iff.2 (Subtype.ext g.2.2)⟩
      left_inv := fun x => rfl
      right_inv := fun g => rfl }


theorem N_le_derived (F : XNFacts) :
    closure ({elemW xC1, elemW xC2} : Set (Equiv.Perm (Fin 1408))) ≤ derivedOf XP := by
  rw [closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact F.c1_mem
  · exact F.c2_mem


end CFSG.EvenSporadicStandard.HNRecog.Section4.XModel
