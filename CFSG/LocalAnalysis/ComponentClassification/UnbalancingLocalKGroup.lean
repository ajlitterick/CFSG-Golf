module

public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.Foundations.Catalog

public section

namespace CFSG.ComponentClassification.UnbalancingLocal

open CFSG.Assembly

abbrev KGroupOver (C : GroupProp) (X : Type) [Group X] : Prop :=
  KCore.KGroupAllSimple C X


theorem inCatalog_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : InCatalog Y) :
    InCatalog X :=
  inCatalog_isoInvariant e h

theorem catalog_of_abelian_simple (S : Type) [Group S] [Finite S] [IsSimpleGroup S]
    (hcomm : ∀ a b : S, a * b = b * a) : Blueprint.Catalog S :=
  SectionRank.catalog_containsAbelianSimple S hcomm

variable {C : GroupProp}


theorem catalog_of_kProper_of_surjective
    (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    {G : Type} [Group G] (hK : KProper C G) (K : Subgroup G) (hKtop : K ≠ ⊤) {S : Type}
    [Group S] [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a) (φ : K →* S)
    (hφ : Function.Surjective φ) : C S :=
  KCore.KProperNonab.catalogue_of_surjective hC hK K hKtop hnonab φ hφ

theorem kGroupOver_of_kProper (hC : ∀ {X Y : Type} [Group X] [Group Y], X ≃* Y → C Y → C X)
    (hab : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∀ a b : S, a * b = b * a) → C S)
    {G : Type} [Group G] [Finite G] (hK : KProper C G) (H : Subgroup G) (hH : H ≠ ⊤) :
    KGroupOver C H :=
  KCore.KProperNonab.kGroupAllSimple hC hab hK H hH


end CFSG.ComponentClassification.UnbalancingLocal
