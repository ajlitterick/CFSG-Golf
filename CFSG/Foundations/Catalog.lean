module

public import CFSG.Assembly.InCatalog
public import CFSG.Foundations.Basic

public section

namespace CFSG

@[expose] def IsKGroup (X : Type) [Group X] : Prop :=
  KCore.KGroupAllSimple Assembly.InCatalog X

@[expose] def IsKProper (X : Type) [Group X] : Prop :=
  ∀ H : Subgroup X, H ≠ ⊤ → IsKGroup H


theorem IsKGroup.subgroup {X : Type} [Group X] (hX : IsKGroup X) (H : Subgroup X) :
    IsKGroup H :=
  KCore.KGroupAllSimple.subgroup Assembly.inCatalog_isoInvariant hX H

theorem IsKGroup.quotient {X : Type} [Group X] (hX : IsKGroup X) (M : Subgroup X) [M.Normal] :
    IsKGroup (X ⧸ M) :=
  KCore.KGroupAllSimple.quotient Assembly.inCatalog_isoInvariant hX M

theorem IsKGroup.of_surjective {X Y : Type} [Group X] [Group Y] (hX : IsKGroup X) (f : X →* Y)
    (hf : Function.Surjective f) : IsKGroup Y :=
  KCore.KGroupAllSimple.of_surjective Assembly.inCatalog_isoInvariant hX f hf

theorem IsKGroup.of_injective {X Y : Type} [Group X] [Group Y] (hY : IsKGroup Y) (f : X →* Y)
    (hf : Function.Injective f) : IsKGroup X :=
  KCore.KGroupAllSimple.of_injective Assembly.inCatalog_isoInvariant hY f hf

theorem IsKGroup.of_mulEquiv {X Y : Type} [Group X] [Group Y] (hY : IsKGroup Y) (e : X ≃* Y) :
    IsKGroup X :=
  KCore.KGroupAllSimple.of_mulEquiv Assembly.inCatalog_isoInvariant hY e

theorem IsKGroup.inCatalog_of_surjective {X : Type} [Group X] (hX : IsKGroup X) (K : Subgroup X)
    {S : Type} [Group S] [IsSimpleGroup S] (φ : K →* S) (hφ : Function.Surjective φ) :
    Assembly.InCatalog S :=
  KCore.KGroupAllSimple.catalogue_of_surjective Assembly.inCatalog_isoInvariant hX K φ hφ


end CFSG
