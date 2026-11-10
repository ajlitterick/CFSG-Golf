module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434Core
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
import CFSG.RankThree.PartTwo.Sec4.Steps434
import CFSG.RankThree.PartTwo.Sec4.Steps439
import CFSG.RankThree.PartTwo.Sec5.Item37
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores

namespace Item434


theorem coprime_orderOf_of_mem {X : Type*} [Group X] [Finite X] {N : Subgroup X}
    (hN : ¬ 3 ∣ Nat.card N) {x : X} (hx : x ∈ N) : Nat.Coprime (orderOf x) 3 := by
  refine (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun h3 => ?_))
  exact hN (h3.trans (by rw [← Subgroup.orderOf_mk x hx]; exact orderOf_dvd_natCard _))

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G}

theorem inf_centralizer_pCore_le (h : Ctx434Core G A M Q) :
    Subgroup.centralizer (layer G : Set G) ⊓ Subgroup.centralizer (CFSG.pCore 3 G : Set G) ≤
      CFSG.pCore 3 G := by
  set C := Subgroup.centralizer (layer G : Set G) with hC
  intro x hx
  have hF := h.rank3II_4_36
  have hmem : (⟨x, hx.1⟩ : C) ∈ Subgroup.centralizer (generalizedFitting C : Set C) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    have hyP : (y : G) ∈ CFSG.pCore 3 G := by
      rw [← hF]
      exact ⟨y, hy, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hx.2 y hyP
  have hx' := CFSG.centralizer_generalizedFitting_le C hmem
  rw [← hF]
  exact ⟨_, hx', rfl⟩

theorem commutator_pCore_eq_bot (h : Ctx434Core G A M Q) : ⁅CFSG.pCore 3 G, Q⁆ = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hQ3, hAQ⟩ := (mem_invariantPiSubgroups_piCompl_iff Nat.prime_three).mp
    h.mem_invariant
  have hPtop : Subgroup.normalizer (CFSG.pCore 3 G : Set G) = ⊤ :=
    Subgroup.normalizer_eq_top (CFSG.pCore 3 G)
  exact Sec5.rank3II_3_7 G 3 Nat.prime_three (by norm_num) A Q (CFSG.pCore 3 G) h.isE27.1 hQ3 hAQ
    CFSG.pCore_isPGroup (by rw [hPtop]; exact le_top) (by rw [hPtop]; exact le_top)
    fun y hy hy3 => h.rank3II_4_35 hy.2 hy3

theorem inf_centralizer_layer_eq_bot (h : Ctx434Core G A M Q) :
    Q ⊓ Subgroup.centralizer (layer G : Set G) = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, hQ3, -⟩ := (mem_invariantPiSubgroups_piCompl_iff Nat.prime_three).mp
    h.mem_invariant
  have hPQ : CFSG.pCore 3 G ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (commutator_pCore_eq_bot h)
  have hle : Q ⊓ Subgroup.centralizer (layer G : Set G) ≤ CFSG.pCore 3 G := by
    intro x hx
    refine inf_centralizer_pCore_le h (Subgroup.mem_inf.mpr ⟨hx.2, ?_⟩)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hPQ hy) x hx.1).symm
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 3) (G := G))
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card (CFSG.pCore 3 G)) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.coprime_comm.mp
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hQ3))
  have hdisj := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  rw [eq_bot_iff, ← hdisj]
  exact le_inf inf_le_left hle


end Item434

namespace Ctx434Core


end Ctx434Core


end CFSG.RankThree.PartTwo.Sec4
