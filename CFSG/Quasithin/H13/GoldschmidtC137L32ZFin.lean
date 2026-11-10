module

public import CFSG.Quasithin.H13.GoldschmidtC137L32ZCase
public import CFSG.Quasithin.H13.GoldschmidtC137L32Off
public import CFSG.Quasithin.H13.GoldschmidtC137L32ZKey

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Quasithin.H13.U3
open scoped Pointwise

variable {G : Type} [Group G]

namespace L32Ctx

variable [Finite G] {X T L P W : Subgroup G} {u : G} (h : L32Ctx X T L P W u)
include h

theorem isTwoReducedIn_of_le {Y : Subgroup G} (hLY : L ≤ Y) (hWY : W ≤ Y)
    (hYN : Y ≤ normalizer (W : Set G)) : IsTwoReducedIn Y W := by
  have hM8 : Nat.card (IntMod W h.hWe) = 8 := h.hW8
  obtain ⟨φ⟩ := S153E58.nonempty_mulEquiv_pi_of_sq_eq_one
    (fun m : IntMod W h.hWe => IntMod.sq_eq_one m) (d := 3) (by rw [hM8]; norm_num)
  have hnp : ¬ IsPGroup 2 (MulAut (IntMod W h.hWe)) := by
    intro hp
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [card_mulAut φ] at hk
    have h168 : ∀ j : ℕ, 2 ^ j ≠ 168 := by
      intro j hj
      have h1 : j < 8 := by
        by_contra hj8
        push Not at hj8
        have : 2 ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj8
        omega
      interval_cases j <;> omega
    exact h168 k hk.symm
  exact isTwoReducedIn_of_autI_top hLY hWY hYN h.hWe (isSimpleGroup_mulAut φ) hnp h.autI_L_top

theorem hWL' : W ≤ L := by
  rw [← h.hWL]
  refine Subgroup.commutator_le.2 fun w hw l hl => ?_
  have h1 : w * l * w⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (h.hn (h.hred.1 hw)) l).1 hl
  have : w * l * w⁻¹ * l⁻¹ ∈ L := L.mul_mem h1 (L.inv_mem hl)
  simpa [commutatorElement_def] using this

theorem hWO : W ≤ pCoreOf 2 L :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 h.hWL' (h.hLX.trans h.hXN)
    (B2F.isPGroup_of_isElemAbelian h.hWe)

theorem pCoreOf_le_sup {S : Subgroup G} (hSX : S ≤ X) : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ S) := by
  have hSnOL : S ≤ normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
    hSX.trans (h.hn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
    (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) hSnOL)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

theorem pCoreOf_sup_le_centralizer {S : Subgroup G} (hSX : S ≤ X) :
    pCoreOf 2 (L ⊔ S) ≤ centralizer (W : Set G) := by
  have hLSX : L ⊔ S ≤ X := sup_le h.hLX hSX
  have hred := h.isTwoReducedIn_of_le (Y := L ⊔ S) le_sup_left (h.hWL'.trans le_sup_left)
    (hLSX.trans h.hXN)
  refine hred.2.2.2 _ (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) fun d hd => ?_
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ S)) ⟨d, hd⟩
  refine ⟨k, ?_⟩
  have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [this]
  exact Subgroup.one_mem _

end L32Ctx

theorem omegaOneCenterOf_le_gc (S' : Subgroup G) :
    omegaOneCenterOf S' ≤ centerOf S' :=
  (Subgroup.closure_le (centerOf S')).2 fun _ hx => hx.1


end CFSG.Quasithin.H13.U3.GC137
