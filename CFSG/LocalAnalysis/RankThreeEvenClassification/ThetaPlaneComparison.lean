module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaQuotientCriterion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaPlaneIndependence

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u


theorem thetaPlaneIntersection_le_alpha_of_fixed_theta
    {G : Type u} [Group G] [Finite G]
    (prime : ℕ) (hprime : prime.Prime) (actor firstPlane secondPlane : Subgroup G)
    (hcomm : IsMulCommutative actor) (hfirstLe : firstPlane ≤ actor)
    (hsecondLe : secondPlane ≤ actor)
    (hsecondPower : ∀ member : secondPlane, member ^ prime = 1)
    (hsecondCard : Nat.card secondPlane = prime ^ 2)
    (element : G) (helement : element ∈ firstPlane) (hne : element ≠ 1)
    (hfixed : ∀ member ∈ secondPlane, member ≠ 1 →
      thetaPlaneIntersection prime firstPlane ⊓ Subgroup.centralizer ({member} : Set G) ≤
        thetaCoreOf prime (Subgroup.centralizer ({member} : Set G))) :
    thetaPlaneIntersection prime firstPlane ≤ thetaPlaneAlpha prime secondPlane := by
  let intersection := thetaPlaneIntersection prime firstPlane
  have hnormalized : secondPlane ≤ Subgroup.normalizer (intersection : Set G) :=
    hsecondLe.trans (actor_normalizes_thetaPlaneIntersection prime hprime actor firstPlane hcomm hfirstLe)
  have hsolvable := thetaPlaneIntersection_solvable prime hprime firstPlane element helement hne
  have hcomplement := thetaPlaneIntersection_prime_complement prime hprime firstPlane element helement hne
  have hcommutatorLe : ⁅intersection, secondPlane⁆ ≤ thetaPlaneAlpha prime secondPlane := by
    rw [repeated_action_commutator_generation prime hprime secondPlane intersection
      (fun first second => Subtype.ext (congrArg (fun value : actor => (value : G))
        (isMulCommutative_iff.mp hcomm ⟨first, hsecondLe first.property⟩
          ⟨second, hsecondLe second.property⟩))) hsecondPower hsecondCard hsolvable hcomplement hnormalized]
    apply iSup_le
    intro member
    apply iSup_le
    intro hmemberNe
    have hmemberAmbientNe : (member : G) ≠ 1 := fun heq => hmemberNe (Subtype.ext heq)
    apply (Subgroup.commutator_mono (hfixed member member.property hmemberAmbientNe) le_rfl).trans
    apply le_sup_of_le_left
    exact le_iSup_of_le (member : G) (le_iSup_of_le member.property
      (le_iSup_of_le hmemberAmbientNe le_rfl))
  have hfixedLe : intersection ⊓ Subgroup.centralizer (secondPlane : Set G) ≤
      thetaPlaneIntersection prime secondPlane := by
    apply le_iInf
    intro member
    apply le_iInf
    intro hmember
    apply le_iInf
    intro hmemberNe
    exact (inf_le_inf le_rfl
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hmember))).trans
      (hfixed member hmember hmemberNe)
  change intersection ≤ thetaPlaneAlpha prime secondPlane
  rw [coprime_commutator_centralizer_factorization prime hprime secondPlane intersection
    (IsPGroup.of_card hsecondCard) hcomplement hnormalized]
  exact sup_le hcommutatorLe (hfixedLe.trans le_sup_right)


end CFSG.RankThreeEvenClassification.Helpers
