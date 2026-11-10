module

public import CFSG.LocalAnalysis.RankThreeEvenClassification.CharacteristicLocal
public import CFSG.LocalAnalysis.RankThreeEvenClassification.QuadraticActions

public section

open CFSG.Open

namespace CFSG.RankThreeEvenClassification.Helpers

universe u v

theorem primeCore_quotient_preimage_congr {G : Type u} [Group G] (prime : ℕ)
    (first second : Subgroup G) [first.Normal] [second.Normal] (heq : first = second) :
    (pCore prime (G ⧸ first)).comap (QuotientGroup.mk' first) =
      (pCore prime (G ⧸ second)).comap (QuotientGroup.mk' second) := by
  subst second
  rfl


theorem primeCore_quotient_preimage_eq_range_preimage {G : Type u} {H : Type v}
    [Group G] [Group H] (prime : ℕ) (homomorphism : G →* H) :
    (pCore prime (G ⧸ homomorphism.ker)).comap (QuotientGroup.mk' homomorphism.ker) =
      (pCore prime homomorphism.range).comap homomorphism.rangeRestrict := by
  let equivalence := QuotientGroup.quotientKerEquivRange homomorphism
  have hmapped := pCore_map_equiv prime equivalence
  have hcomap := congrArg (fun subgroup : Subgroup homomorphism.range =>
    subgroup.comap equivalence.toMonoidHom) hmapped
  have hinjective : Function.Injective equivalence.toMonoidHom := equivalence.injective
  rw [Subgroup.comap_map_eq_self_of_injective (f := equivalence.toMonoidHom) hinjective] at hcomap
  rw [hcomap, Subgroup.comap_comap]
  have hcompose : equivalence.toMonoidHom.comp (QuotientGroup.mk' homomorphism.ker) =
      homomorphism.rangeRestrict := by
    ext member
    rfl
  rw [hcompose]

theorem actionPrimeCore_eq_range_preimage {actor : Type u} {acted : Type v}
    [Group actor] [Group acted] (prime : ℕ) (action : actor →* MulAut acted) :
    actionPrimeCore prime action = (pCore prime action.range).comap action.rangeRestrict :=
  primeCore_quotient_preimage_eq_range_preimage prime action

end CFSG.RankThreeEvenClassification.Helpers
