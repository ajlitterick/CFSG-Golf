module

public import CFSG.LocalAnalysis.ComponentClassification.SylowProductSandwich
public import CFSG.LocalAnalysis.ComponentClassification.BlockFixedFactorSizeSandwich

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockFixedFactorSylowReduction

structure Context {G : Type*} [Group G]
    (component : Subgroup G) (actor : G) (fixed : Subgroup G)
    (rank : ℕ) (elementary opposite : Subgroup G) : Prop where
  even : Even (Nat.card component)
  universal : UniversalComponentBlock.Universal component
  quasisimple : IsQuasisimple component
  card : 3 ≤ Nat.card ↥(UniversalOrbitBlock.block component)
  odd : Odd (Nat.card ↥(UniversalOrbitBlock.block component))
  control : BlockFactorContainment.ExternalControl component
  outside : actor ∉ UniversalOrbitBlock.normalizer component
  fixed_mem : fixed ∈ UniversalOrbitBlock.block component
  normalizes : ∀ first ∈ UniversalOrbitBlock.block component,
    first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom ≤
      Subgroup.normalizer (UniversalOrbitBlock.conjugate fixed actor : Set G)
  positive : 1 ≤ rank
  original : BlockCommonInvolutionPackage.Common component
    ((UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom) rank elementary
  opposite : BlockCommonInvolutionPackage.Common (UniversalOrbitBlock.conjugate component actor)
    (UniversalOrbitBlock.normalizer component) rank opposite
  forward_strict : ∀ first ∈ UniversalOrbitBlock.block component,
    ∀ left : Sylow 2 ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom),
    ∀ right : Sylow 2 first,
      Nat.card (left : Subgroup ↥(first ⊓
        (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) <
          Nat.card (right : Subgroup first)
  reverse_strict : ∀ left : Sylow 2 ↥(UniversalOrbitBlock.conjugate fixed actor ⊓ UniversalOrbitBlock.normalizer component),
    ∀ right : Sylow 2 (UniversalOrbitBlock.conjugate fixed actor),
      Nat.card (left : Subgroup ↥(UniversalOrbitBlock.conjugate fixed actor ⊓ UniversalOrbitBlock.normalizer component)) <
        Nat.card (right : Subgroup (UniversalOrbitBlock.conjugate fixed actor))

theorem Context.upper {G : Type*} [Group G] [Finite G]
    {component fixed elementary opposite : Subgroup G} {actor : G} {rank : ℕ}
    (context : Context component actor fixed rank elementary opposite)
    (prescribed : Sylow 2 ↥(UniversalOrbitBlock.conjugate fixed actor ⊓ UniversalOrbitBlock.normalizer component))
    (first : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component)
    (sylow : Sylow 2 ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) :
    Nat.card (sylow : Subgroup ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) ≤
      Nat.card (prescribed : Subgroup ↥(UniversalOrbitBlock.conjugate fixed actor ⊓ UniversalOrbitBlock.normalizer component)) :=
  BlockFixedFactorSizeSandwich.upper component context.even context.universal context.quasisimple context.card context.control
    actor context.outside fixed context.fixed_mem context.normalizes rank context.positive elementary context.original
      context.reverse_strict prescribed first hfirst sylow


theorem Context.exceptional {G : Type*} [Group G] [Finite G]
    {component fixed elementary opposite : Subgroup G} {actor : G} {rank : ℕ}
    (context : Context component actor fixed rank elementary opposite)
    (fixedSylow : Sylow 2 ↥(UniversalOrbitBlock.conjugate fixed actor ⊓ UniversalOrbitBlock.normalizer component))
    (anchor : Subgroup G) (hanchor : anchor ∈ UniversalOrbitBlock.block component)
    (hsize : ∀ sylow : Sylow 2 ↥(anchor ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom),
      Nat.card (sylow : Subgroup ↥(anchor ⊓
        (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) =
          Nat.card (fixedSylow : Subgroup ↥(UniversalOrbitBlock.conjugate fixed actor ⊓ UniversalOrbitBlock.normalizer component)))
    (first : Subgroup G) (hfirst : first ∈ UniversalOrbitBlock.block component) (hdistinct : anchor ≠ first)
    (anchorSylow : Sylow 2 ↥(anchor ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom))
    (firstSylow : Sylow 2 ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)) :
    (firstSylow : Subgroup ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)).map
        (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).subtype ≤
      (anchorSylow : Subgroup ↥(anchor ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)).map
        (anchor ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).subtype ∧
    (firstSylow : Subgroup ↥(first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom)).map
        (first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom).subtype ≤
      (Subgroup.center first).map first.subtype := by
  let anchorOverlap := anchor ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom
  let firstOverlap := first ⊓ (UniversalOrbitBlock.normalizer component).map (MulAut.conj actor).toMonoidHom
  let anchorTwo := (anchorSylow : Subgroup anchorOverlap).map anchorOverlap.subtype
  let firstTwo := (firstSylow : Subgroup firstOverlap).map firstOverlap.subtype
  have hanchorBound : anchorTwo ≤ anchorOverlap := Subgroup.map_subtype_le _
  have hfirstBound : firstTwo ≤ firstOverlap := Subgroup.map_subtype_le _
  have hbound := BlockPairOrderBounds.reverse component context.even context.universal context.quasisimple context.card
    context.control anchor first fixed hanchor hfirst context.fixed_mem hdistinct actor context.outside anchorTwo firstTwo
      (anchorSylow.isPGroup'.map anchorOverlap.subtype) (firstSylow.isPGroup'.map firstOverlap.subtype)
        (BlockCommonSylowNontrivial.image_ne_bot context.original context.positive anchor hanchor anchorSylow)
          (hanchorBound.trans inf_le_left) (hfirstBound.trans inf_le_left)
            (hanchorBound.trans (context.normalizes anchor hanchor)) (hfirstBound.trans (context.normalizes first hfirst))
              context.reverse_strict fixedSylow
  have hanchorSize : Nat.card anchorTwo = Nat.card (fixedSylow : Subgroup ↥(UniversalOrbitBlock.conjugate fixed actor ⊓
      UniversalOrbitBlock.normalizer component)) := by
    rw [Subgroup.card_map_of_injective anchorOverlap.subtype_injective]
    exact hsize anchorSylow
  obtain ⟨_, hcontained⟩ := SylowProductSandwich.collapse anchorTwo firstTwo _ hanchorSize hbound
  exact ⟨hcontained, SylowProductSandwich.intersection_center first anchor
    (UniversalOrbitBlock.block_commutes component context.even context.universal first hfirst anchor hanchor hdistinct.symm)
      firstTwo (hfirstBound.trans inf_le_left) (hcontained.trans (hanchorBound.trans inf_le_left))⟩


end CFSG.ComponentClassification.BlockFixedFactorSylowReduction
