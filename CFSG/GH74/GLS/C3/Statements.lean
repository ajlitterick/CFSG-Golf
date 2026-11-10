module

public import CFSG.GH74.GLS.Gen4Exclusions

public section

namespace CFSG.GH74.GLS

open Blueprint Assembly.LowTwoRank

structure C3Hyp (G : Type) [Group G] [Finite G] : Prop where
  kproper : IsKProperSimple G
  gen4 : Gen4 G
  kgh : KGH G
  lt2o : IsLT2oType G
  notRE : ¬ IsRestrictedEvenType G

theorem C3Hyp.pRank_eq_four {G : Type} [Group G] [Finite G] (h : C3Hyp G) : pRank 2 G = 4 :=
  le_antisymm h.gen4.pRank_two_le h.lt2o.1

@[expose] def S_C3_gen4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], C3Hyp G →
    Nonempty (G ≃* alternatingGroup (Fin 9)) ∨ Nonempty (G ≃* alternatingGroup (Fin 10)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 11))


theorem c23List_of_lb2_branch_gen4 {G : Type} [Group G] [Finite G] (hG : IsKProperSimple G)
    (hgen : Gen4 G) (hK : KGH G) (hSO : IsSpecialOddType G) (hC3 : S_C3_gen4)
    (hLB : IsLB2Type G → C23List G) : C23List G := by
  have hsub := l2Sub_of_not_l2Meets_g2 hG hSO.2
  by_cases hB : L2Meets G InB2 ∨ pRank 2 G ≤ 3
  · exact hLB ⟨hsub, hB, hSO.1⟩
  · rw [not_or] at hB
    have hrank : 4 ≤ pRank 2 G := by omega
    have hLT : IsLT2oType G := by
      refine ⟨hrank, fun x hx K hK => ?_⟩
      rcases hsub x hx K hK with h | h
      · exact Or.inl h
      · refine Or.inr (inU2_of_inT2_of_center_bot h ?_)
        by_contra hz
        exact hB.1 ⟨x, hx, K, hK, ⟨h, hz⟩⟩
    rcases hC3 G ⟨hG, hgen, hK, hLT, hSO.1⟩ with h | h | h
    · exact C23List.of_alt9 h
    · exact C23List.of_alt10 h
    · exact C23List.of_alt11 h


end CFSG.GH74.GLS
