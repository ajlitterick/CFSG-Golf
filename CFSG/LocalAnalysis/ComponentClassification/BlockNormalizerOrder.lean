module

public import CFSG.LocalAnalysis.ComponentClassification.BlockTransitivity
public import CFSG.LocalAnalysis.ComponentClassification.InnerActionOrder
public import CFSG.LocalAnalysis.ComponentClassification.GroupTwoPart

public section

open CFSG.Open

namespace CFSG.ComponentClassification.BlockNormalizerOrder

@[expose] noncomputable def action {G : Type*} [Group G] (component : Subgroup G) :
    Subgroup.normalizer (component : Set G) →* MulAut (component ⧸ Subgroup.center component) :=
  (PerfectAutomorphisms.centerQuotientHom component).comp component.normalizerMonoidHom

theorem kernel {G : Type*} [Group G] (component : Subgroup G) (hquasisimple : IsQuasisimple component) :
    (action component).ker = (Subgroup.centralizer (component : Set G)).subgroupOf (Subgroup.normalizer (component : Set G)) := by
  let : Group.IsPerfect component := ⟨hquasisimple.1⟩
  exact (MonoidHom.ker_comp_of_injective component.normalizerMonoidHom (PerfectAutomorphisms.centerQuotientHom component)
    (PerfectAutomorphisms.centerQuotientHom_injective component)).trans (Subgroup.normalizerMonoidHom_ker component)

theorem card {G : Type*} [Group G] [Finite G]
    (component : Subgroup G) (heven : Even (Nat.card component))
    (huniversal : UniversalComponentBlock.Universal component) (hquasisimple : IsQuasisimple component) :
    Nat.card (UniversalOrbitBlock.normalizer component) = Nat.card (Subgroup.centralizer (component : Set G)) *
      Nat.card (action component).range * Nat.card ↥(UniversalOrbitBlock.block component) := by
  have hkernelCard : Nat.card (action component).ker = Nat.card (Subgroup.centralizer (component : Set G)) := by
    rw [kernel component hquasisimple]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.centralizer_le_normalizer _)).toEquiv
  have hnormalizerCard := (action component).ker.card_mul_index
  rw [Subgroup.index_ker, hkernelCard] at hnormalizerCard
  rw [BlockTransitivity.card component heven huniversal hquasisimple component (UniversalOrbitBlock.mem_block_self component),
    ← hnormalizerCard]

theorem inner_le {G : Type*} [Group G] (component : Subgroup G) :
    OuterAutomorphisms.inner (component ⧸ Subgroup.center component) ≤ (action component).range := by
  rintro automorphism ⟨element, rfl⟩
  obtain ⟨lift, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center component) element
  let actor : Subgroup.normalizer (component : Set G) := ⟨lift.val, Subgroup.le_normalizer lift.property⟩
  refine ⟨actor, ?_⟩
  have hnormalizer : component.normalizerMonoidHom actor = MulAut.conj lift := by
    ext member
    rfl
  change PerfectAutomorphisms.centerQuotientHom component (component.normalizerMonoidHom actor) = _
  rw [hnormalizer, OuterAutomorphisms.centerQuotient_conj]


end CFSG.ComponentClassification.BlockNormalizerOrder
