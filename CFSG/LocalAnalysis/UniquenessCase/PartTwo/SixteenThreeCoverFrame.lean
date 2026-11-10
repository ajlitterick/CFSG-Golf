module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.SylowThreeFrame
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThreeCovers
import CFSG.GroupTheory.CoprimeCentralizerRank
import CFSG.GroupTheory.PGroup.CardCoprime
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace SylowThreeData


end SylowThreeData

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem map_conj_mem_three_calC_of_pRank_le_three {M : Subgroup G}
    (K : Fin 3 → Subgroup G) (hK : ∀ i, K i ∈ calC M)
    (hKi : Function.Injective K)
    (hK3 : ∀ i, CFSG.Open.pRank 3 (K i) = 1)
    (hM3 : CFSG.Open.pRank 3 M ≤ 3)
    {m : G} (hm : m ∈ M) (i : Fin 3) :
    ∃ j, (K i).map (MulAut.conj m).toMonoidHom = K j := by
  classical
  let f : MulAut G := MulAut.conj m
  let L : Subgroup G := (K i).map f.toMonoidHom
  have hMmap : M.map f.toMonoidHom = M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.mem_normalizer_iff_map_conj.mp
      (Subgroup.le_normalizer hm)
  have hL : L ∈ calC M :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.calC_map M f hMmap (hK i)
  have hL3 : CFSG.Open.pRank 3 L = 1 := by
    show CFSG.Open.pRank 3 ((K i).map f.toMonoidHom) = 1
    rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_pRank_map_aut 3 (K i) f, hK3 i]
  by_contra hcon
  push Not at hcon
  have h01 : K 0 ≠ K 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hKi h)
  have h02 : K 0 ≠ K 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hKi h)
  have h12 : K 1 ≠ K 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hKi h)
  have hcard3 : ({K 0, K 1, K 2} : Finset (Subgroup G)).card = 3 :=
    Finset.card_eq_three.2 ⟨K 0, K 1, K 2, h01, h02, h12, rfl⟩
  have hnot : L ∉ ({K 0, K 1, K 2} : Finset (Subgroup G)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h | h)
    exacts [hcon 0 h, hcon 1 h, hcon 2 h]
  let S : Finset (Subgroup G) := insert L {K 0, K 1, K 2}
  have hcard : S.card = 4 := by
    rw [show S = insert L {K 0, K 1, K 2} from rfl, Finset.card_insert_of_notMem hnot, hcard3]
  have hS : ∀ A ∈ S, A ∈ calC M := by
    intro A hA
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl | rfl
    exacts [hL, hK 0, hK 1, hK 2]
  have hZ : ∀ A ∈ S, ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 A)) := by
    intro A hA
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl | rfl
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_not_dvd_card_center_bar2
        hL.2.2 (le_of_eq hL3)
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_not_dvd_card_center_bar2
        (hK 0).2.2 (le_of_eq (hK3 0))
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_not_dvd_card_center_bar2
        (hK 1).2.2 (le_of_eq (hK3 1))
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_not_dvd_card_center_bar2
        (hK 2).2.2 (le_of_eq (hK3 2))
  have hd : ∀ A ∈ S, 3 ∣ Nat.card A := by
    intro A hA
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hA
    rcases hA with rfl | rfl | rfl | rfl
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_three_dvd_card_of_pRank_eq_one hL3
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_three_dvd_card_of_pRank_eq_one (hK3 0)
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_three_dvd_card_of_pRank_eq_one (hK3 1)
    · exact CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_three_dvd_card_of_pRank_eq_one (hK3 2)
  have hle := P22fin3.card_le_pRank_of_finset (X := M) (S := S) Nat.prime_three (by norm_num)
    hS hZ hd
  rw [hcard] at hle
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
