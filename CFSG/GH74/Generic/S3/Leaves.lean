module

public import CFSG.GH74.Generic.S3.Defs
public import CFSG.GH74.GLS.LU.Ident

public section

namespace CFSG.GH74.Generic.S3

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.Blueprint Subgroup


@[expose] def B_S3_L4Reflection_lin : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Gen4 G → ∀ (F : Type) (_ : Field F) (_ : Finite F) (p f : ℕ),
    p.Prime → p ≠ 2 → Nat.card F = p ^ f → 5 ≤ p ^ f → p ^ f % 4 = 1 →
      ∀ (x z u : G) (Y : Fin 3 → Subgroup G), orderOf x = 2 →
        GLS.LU.IsLinearA3Neighborhood F z u Y → A3Reflection x u Y → False

@[expose] def B_S3_L4Reflection_uni : Prop :=
  ∀ (G : Type) [Group G] [Finite G], Gen4 G → ∀ (F₂ F : Type) (_ : Field F₂) (_ : Finite F₂)
    (_ : Field F) (_ : Finite F) (p f : ℕ),
    p.Prime → p ≠ 2 → Nat.card F₂ = (p ^ f) ^ 2 → Nat.card F = p ^ f → 5 ≤ p ^ f → p ^ f % 4 = 3 →
      ∀ (x z u : G) (Y : Fin 3 → Subgroup G), orderOf x = 2 →
        GLS.LU.IsUnitaryA3Neighborhood (p ^ f) F₂ F z u Y → A3Reflection x u Y → False

@[expose] def B_S3_L4Reflection : Prop :=
  B_S3_L4Reflection_lin ∧ B_S3_L4Reflection_uni

end CFSG.GH74.Generic.S3
