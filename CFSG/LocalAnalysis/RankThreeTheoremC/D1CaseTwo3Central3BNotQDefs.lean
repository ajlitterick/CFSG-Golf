module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerSplit
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111DataBridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers
open Hyp111

variable {G : Type} [Group G] [Finite G]

@[expose] def innerNotQJ (p : ℕ) (H : Subgroup G)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
    Subgroup (H ⧸ primeComplementCore (G := H) p) :=
  Subgroup.normalClosure (L : Set (H ⧸ primeComplementCore (G := H) p))


theorem innerNotQJ_eq_of_normal (p : ℕ) (H : Subgroup G)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) [L.Normal] : innerNotQJ p H L = L :=
  Subgroup.normalClosure_eq_self L

structure InnerNotQConfig (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)) (z : H)
    (L : Subgroup (H ⧸ primeComplementCore (G := H) p)) (E : Subgroup G) : Prop where
  cfg : D1ComponentConfig3 p P M H R Rbar
  cyclic : ∀ L' : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf L' ⊤ →
    IsCyclic ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ L' :
      Subgroup (H ⧸ primeComplementCore (G := H) p))
  cand : D1CaseTwoCand p M H R z
  central : ∃ m ∈ M, (P : Subgroup G).map (MulAut.conj m).toMonoidHom ≤
    Subgroup.centralizer ({(z : G)} : Set G)
  notAlphaR : ¬ D1CaseTwoAlphaR p M H R
  isComponent : IsComponentOf L ⊤
  not_le : ¬ L ≤ d1X0 p M H
  fieldOmega : IsFieldOmegaA p M H R L E
  gamma : rankThreeGamma 1 p E ≤ M


end CFSG.LocalAnalysis.RankThreeTheoremC
