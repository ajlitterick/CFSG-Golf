module

public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

structure Ctx434Core (G : Type) [Group G] [Finite G] (A M Q : Subgroup G) : Prop where
  isE27 : Late.IsE27 A
  gamma_le : gamma 2 A ≤ M
  theta_eq_bot : aschbacherSolvableCore 3 G = ⊥
  pRank_eq : CFSG.Open.pRank 3 M = 3
  mem_invariant : Q ∈ invariantPiSubgroups ⊤ A (piCompl 3)
  ne_bot : Q ≠ ⊥
  isQuasisimple : IsQuasisimple (layer G)
  not_le : ¬ layer G ≤ M

theorem Ctx434.toCore {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} (h : Ctx434 G A M Q) :
    Ctx434Core G A M Q :=
  ⟨h.isE27, h.gamma_le, h.theta_eq_bot, h.pRank_eq, h.mem_invariant, h.ne_bot, h.isQuasisimple,
    h.not_le⟩


@[expose] def Item4_34Sec : Prop :=
  ∀ (G₀ : Type) [Group G₀] [Finite G₀], SectionFourHyp G₀ →
    ∀ (H : Subgroup G₀) (G : Type) [Group G] [Finite G] (f : H →* G), Function.Surjective f →
      ¬ 3 ∣ Nat.card f.ker → ∀ A M Q : Subgroup G, Ctx434Core G A M Q → Concl434 A Q


end CFSG.RankThree.PartTwo.Sec4
