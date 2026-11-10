module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepsNHJ
public import CFSG.RankThree.PartTwo.Sec14.Item148ProofYB
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec14.Item145BotNo135
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem allPointsHJ_of_isLBConfig (h134 : Item134)
    (hJ2 : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) {B L' : Subgroup G} {b d : G} (hc : IsLBConfig A B b d L')
    (hB : IsHyperplane A B) : AllPointsHJ A := by
  have hA : Late.IsE27 A := h.isE27
  obtain ⟨-, hd1⟩ := hc.ne_one hB hA
  obtain ⟨hBbd, hbΩ, hLb, ⟨φ⟩, hdL, S, hdS, hSd⟩ := hc
  have hdA : d ∈ A := hB.1 (hBbd ▸ Subgroup.subset_closure (Set.mem_insert_of_mem b rfl))
  have hL'mem : L' ∈ lA A b := hLb ▸ Set.mem_singleton L'
  have hc0 : Subgroup.center (↥L' ⧸ CFSG.pCore 2 ↥L') = ⊥ := by
    have hmap := Subgroup.map_center_eq φ
    rw [hJ2c] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).mp hmap
  have hq := isQuasisimple_of_mulEquiv_nativeJ2 hJ2 hJ2c φ
  have hθ := aschbacherSolvableCore_eq_pCore_two hq hc0
  have hJ2θ : Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃*
      CFSG.Blueprint.NativeSporadic.J2) :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hθ).trans φ⟩
  intro e he
  exact exists_hj_of_hj_point h134 h48 h415 h hbΩ hL'mem hJ2θ hdA hd1 ⟨hdL, S, hdS, hSd⟩ he

theorem lB_eq_bot_of_not_allPointsHJ (h134 : Item134)
    (hJ2 : IsSimpleGroup CFSG.Blueprint.NativeSporadic.J2) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15)
    (hJ2c : Subgroup.center CFSG.Blueprint.NativeSporadic.J2 = ⊥) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (hNHJ : ¬ AllPointsHJ A) {B : Subgroup G} (hB : IsHyperplane A B) :
    lB A B = ⊥ :=
  lB_eq_bot fun _ _ _ hc => hNHJ (allPointsHJ_of_isLBConfig h134 hJ2 h48 h415 hJ2c h hc hB)

section Certificates


end Certificates

end CFSG.RankThree.PartTwo.Sec14
