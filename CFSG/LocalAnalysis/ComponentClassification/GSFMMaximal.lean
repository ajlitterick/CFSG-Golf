module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitFooteBridge
public import CFSG.LocalAnalysis.ComponentClassification.GSLitAssembly

public section

namespace CFSG.ComponentClassification.GSFM

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.GSLit


variable {G : Type*} [Group G] [Finite G]


theorem footeMaximal_of_b2Setting {G : Type} [Group G] [Finite G] {a : G} {J S : Subgroup G}
    (h : B2Setting a J S) : FooteLit.FooteMaximal J :=
  ⟨⟨a, h.orderOf_eq, h.le_centralizer, h.isPComponent⟩, fun _ hM =>
    GrSLit.zStar_equiv_of_weakReach h (GrSLit.gsWeakReach_of_footeReach hM)⟩

theorem exists_footeMaximal_component_of_small_types
    (hTB : ThompsonBurgoyneInput)
    (hSA : SolAltLit.SolomonAlternatingOddInput) (hB : TheoremBBoundedInput) (hH : HarrisInput)
    (hGF : GloballyFirstRankTwoInput)
    (X : Type) [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X)
    (hsmall : ¬ ∃ (x y : X) (L : Subgroup X), GSUnbalancingTriple x y L ∧
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* Blueprint.NativeSporadic.He) ∨
        Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 3 2 2))
    (htriple : ∃ (a b : X) (J : Subgroup X), GSUnbalancingTriple a b J) :
    ∃ (x y : X) (L : Subgroup X), GSMaximalUnbalancingTriple x y L ∧ GSMaximalComponent L ∧
      FooteLit.FooteMaximal L ∧
      (Nonempty (L ⧸ pPrimeCore 2 L ≃* alternatingGroup (Fin 7)) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          Blueprint.LieModel (L ⧸ pPrimeCore 2 L) .PSL 2 p f) := by
  obtain ⟨a, x, J, hJ, hbound⟩ :=
    exists_maximal_unbalancing_triple_bounded hTB hSA hGF hnonab hK hz hU htriple
  have htype := unbalancing_component_type_of_small hTB hSA hnonab hK hz hU hsmall hJ.1
  suffices hmax : GSMaximalComponent J ∧ FooteLit.FooteMaximal J from
    ⟨a, x, J, hJ, hmax.1, hmax.2, htype⟩
  rcases hB X hnonab hK hz hU a x J hJ hbound (htype.imp id Or.inl) with
    ⟨-, b, L, ρ, e, hb, hLb, hL, hρ, hρ2, he, hLie, hbK, hP⟩ | ⟨hiso, hcentral⟩
  · refine absurd ⟨b, L, hb, hLb, hL, gsMaximalComponent_of_cyclic_kernel hb hLb hL hP,
      ⟨ρ, 2 * e, hρ, hρ2, by omega, ?_, hLie⟩, isCyclic_sylow_of_eq_zpowers hbK hP⟩
      (hH X hnonab hK hz hU)
    have h3 : 3 ≤ ρ := by have := hρ.two_le; omega
    calc 5 ≤ 3 ^ 2 := by norm_num
      _ ≤ ρ ^ 2 := Nat.pow_le_pow_left h3 2
      _ ≤ ρ ^ (2 * e) := Nat.pow_le_pow_right hρ.pos (by omega)
  · exact ⟨gsMaximalComponent_of_B2 hJ.1.1 hJ.1.2.2.2.1 hJ.1.2.2.2.2.1 hiso hcentral,
      GrSLit.footeMaximal_of_B2 hJ.1.1 hJ.1.2.2.2.1 hJ.1.2.2.2.2.1 hiso hcentral⟩

end CFSG.ComponentClassification.GSFM
