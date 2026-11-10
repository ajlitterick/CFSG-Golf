module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitMaximal

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type*} [Group G]

@[expose] def FootePointedStep (a : G) (L : Subgroup G) (b : G) (K : Subgroup G) : Prop :=
  IsTwoComponentAt a L ∧ IsTwoComponentAt b K ∧ a * b = b * a ∧ a ≠ b ∧
    b ∈ coreActionKernel L ∧ conjClosure (footeFixed L b) (twoLayerOf b) = K ⊔ conjugate K a

@[expose] def FootePointedReach (a : G) (L : Subgroup G) (b : G) (K : Subgroup G) : Prop :=
  Relation.ReflTransGen (fun p q : G × Subgroup G => FootePointedStep p.1 p.2 q.1 q.2) (a, L)
    (b, K)

@[expose] def FootePointedMaximal (t : G) (L : Subgroup G) : Prop :=
  IsTwoComponentAt t L ∧ ∀ (b : G) (K : Subgroup G), FootePointedReach t L b K →
    Nonempty (L ⧸ Open.fusionZStar L ≃* K ⧸ Open.fusionZStar K)

theorem FootePointedStep.footeStep {a b : G} {L K : Subgroup G}
    (h : FootePointedStep a L b K) : FooteStep L K :=
  ⟨a, b, h⟩

theorem FootePointedReach.single {a b : G} {L K : Subgroup G} (h : FootePointedStep a L b K) :
    FootePointedReach a L b K :=
  Relation.ReflTransGen.single h

theorem FootePointedReach.trans {a b c : G} {L K M : Subgroup G}
    (h₁ : FootePointedReach a L b K) (h₂ : FootePointedReach b K c M) :
    FootePointedReach a L c M :=
  Relation.ReflTransGen.trans h₁ h₂

theorem FootePointedReach.footeReach {a b : G} {L K : Subgroup G}
    (h : FootePointedReach a L b K) : FooteReach L K :=
  Relation.ReflTransGen.lift (p := FooteStep) (fun p : G × Subgroup G => p.2)
    (fun _ _ hst => FootePointedStep.footeStep hst) _ _ h

theorem FootePointedReach.target {a b : G} {L K : Subgroup G} (hL : IsTwoComponentAt a L)
    (h : FootePointedReach a L b K) : IsTwoComponentAt b K := by
  rcases Relation.ReflTransGen.cases_tail h with hpq | ⟨p, -, hstep⟩
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpq
    exact hL
  · exact hstep.2.1

theorem FooteMaximal.pointed {t : G} {L : Subgroup G} (hL : FooteMaximal L)
    (ht : IsTwoComponentAt t L) : FootePointedMaximal t L :=
  ⟨ht, fun _ K h => hL.2 K h.footeReach⟩

theorem FootePointedMaximal.of_reach {t b : G} {L K : Subgroup G}
    (hL : FootePointedMaximal t L) (h : FootePointedReach t L b K) : FootePointedMaximal b K := by
  refine ⟨h.target hL.1, fun c M hM => ?_⟩
  obtain ⟨eK⟩ := hL.2 b K h
  obtain ⟨eM⟩ := hL.2 c M (h.trans hM)
  exact ⟨eK.symm.trans eM⟩

theorem FootePointedMaximal.equiv_of_step {t b : G} {L K : Subgroup G}
    (hL : FootePointedMaximal t L) (h : FootePointedStep t L b K) :
    Nonempty (L ⧸ Open.fusionZStar L ≃* K ⧸ Open.fusionZStar K) :=
  hL.2 b K (FootePointedReach.single h)


end CFSG.ComponentClassification.FooteLit
