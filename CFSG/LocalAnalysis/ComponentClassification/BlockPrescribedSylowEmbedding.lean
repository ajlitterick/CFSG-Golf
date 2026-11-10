module

public import CFSG.LocalAnalysis.ComponentClassification.BlockStrictSylowIntersections
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionPrescribedSylowEmbedding

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockPrescribedSylowEmbedding

theorem product {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component)
    (hcard : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component))
    (hcontrol : BlockFactorContainment.ExternalControl component)
    (first second third : Subgroup G)
    (hfirst : first ∈ UniversalOrbitBlock.block component)
    (hsecond : second ∈ UniversalOrbitBlock.block component)
    (hthird : third ∈ UniversalOrbitBlock.block component) (hdistinct : second ≠ third)
    (actor : G) (hactor : actor ∉ UniversalOrbitBlock.normalizer component)
    (firstTwo secondTwo : Subgroup G)
    (hfirstTwo : IsPGroup 2 firstTwo) (hsecondTwo : IsPGroup 2 secondTwo)
    (hne : firstTwo ≠ ⊥)
    (hfirstContained : firstTwo ≤ UniversalOrbitBlock.conjugate second actor)
    (hsecondContained : secondTwo ≤ UniversalOrbitBlock.conjugate third actor)
    (hfirstNormalizes : firstTwo ≤ Subgroup.normalizer (first : Set G))
    (hsecondNormalizes : secondTwo ≤ Subgroup.normalizer (first : Set G))
    (hstrict : ∀ firstSylow : Sylow 2 ↥(first ⊓
      (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom), ∀ secondSylow : Sylow 2 first,
        Nat.card (firstSylow : Subgroup ↥(first ⊓
          (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) <
            Nat.card (secondSylow : Subgroup first))
    (prescribed : Sylow 2 ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) :
    IsMulCommutative ↥(firstTwo ⊔ secondTwo) ∧
      ∃ homomorphism : ↥(firstTwo ⊔ secondTwo) →*
        Subgroup.center ((prescribed : Subgroup ↥(first ⊓
          (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)).map
            (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).subtype),
        Function.Injective homomorphism := by
  obtain ⟨hnormalizes, htwo, _, hnormalizesIntersection, hdisjoint, _, hcentralizers, hcommutator, _⟩ :=
    BlockTwoProductAction.action component heven huniversal hquasisimple hcard hcontrol first second third
      hfirst hsecond hthird hdistinct actor hactor firstTwo secondTwo hfirstTwo hsecondTwo hne hfirstContained hsecondContained
        hfirstNormalizes hsecondNormalizes
  obtain ⟨homomorphism, hinjective⟩ := TwoActionPrescribedSylowEmbedding.embedding first (firstTwo ⊔ secondTwo)
    (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) inf_le_left htwo hdisjoint
      hnormalizes hnormalizesIntersection hcentralizers hcommutator hstrict prescribed
  exact ⟨TwoActionDisplacementEmbedding.abelian_of_embedding homomorphism hinjective, homomorphism, hinjective⟩


end CFSG.ComponentClassification.BlockPrescribedSylowEmbedding
