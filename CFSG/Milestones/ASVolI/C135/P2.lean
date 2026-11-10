module

public import CFSG.Milestones.ASVolI.C1
public import CFSG.Quasithin.Vol2.Ch4Sec3C135H1
public import CFSG.Quasithin.MS93.ASC134

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
open CFSG.Quasithin.H13.Ch4.C135 (dualHom coe_dualHom dualHom_dualHom
  eq_zero_of_dual_equivariant)
open scoped Matrix

variable {G : Type} [Group G]

section Stab

variable {F : Type} [Field F]


end Stab

section Struct

structure burnsideC135_DSG (Q L W₁ W₂ : Subgroup G) {F : Type} [Field F]
    (α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F)
    (βU : ↥(centerOf Q) →* Multiplicative (Fin 3 → F))
    (β₁ : ↥W₁ →* Multiplicative (Fin 3 → F))
    (β₂ : ↥W₂ →* Multiplicative (Fin 3 → F)) : Prop where
  alpha_onto : Function.Surjective α
  normQ : L ≤ Subgroup.normalizer (Q : Set G)
  le₁ : centerOf Q ≤ W₁
  le₂ : centerOf Q ≤ W₂
  le_Q₁ : W₁ ≤ Q
  le_Q₂ : W₂ ≤ Q
  join : W₁ ⊔ W₂ = Q
  meet : W₁ ⊓ W₂ = centerOf Q
  norm₁ : L ≤ Subgroup.normalizer (W₁ : Set G)
  norm₂ : L ≤ Subgroup.normalizer (W₂ : Set G)
  natU_onto : Function.Surjective βU
  natU_ker : βU.ker = ⊥
  natU_act : ∀ (ℓ : ↥L) (u v : ↥(centerOf Q)), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (βU v) =
      ((α ℓ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
        (Multiplicative.toAdd (βU u))
  dual₁_onto : Function.Surjective β₁
  dual₁_ker : β₁.ker = (centerOf Q).subgroupOf W₁
  dual₁_act : ∀ (ℓ : ↥L) (u v : ↥W₁), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (β₁ v) =
      (((α ℓ)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose.mulVec
        (Multiplicative.toAdd (β₁ u))
  dual₂_onto : Function.Surjective β₂
  dual₂_ker : β₂.ker = (centerOf Q).subgroupOf W₂
  dual₂_act : ∀ (ℓ : ↥L) (u v : ↥W₂), (v : G) = ℓ * u * ℓ⁻¹ →
    Multiplicative.toAdd (β₂ v) =
      (((α ℓ)⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).transpose.mulVec
        (Multiplicative.toAdd (β₂ u))

variable {L W₁ W₂ : Subgroup G} {F : Type} [Field F]
  {α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F}
  {βU : ↥(centerOf (pCoreOf 2 L)) →* Multiplicative (Fin 3 → F)}
  {β₁ : ↥W₁ →* Multiplicative (Fin 3 → F)} {β₂ : ↥W₂ →* Multiplicative (Fin 3 → F)}


end Struct

section Split

variable [Finite G] {Q L W₁ W₂ : Subgroup G} {F : Type} [Field F] [Fintype F] [CharP F 2]
  {α : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F}
  {βU : ↥(centerOf Q) →* Multiplicative (Fin 3 → F)}
  {β₁ : ↥W₁ →* Multiplicative (Fin 3 → F)} {β₂ : ↥W₂ →* Multiplicative (Fin 3 → F)}


theorem burnsideC135_βU_injective
    (hD : burnsideC135_DSG Q L W₁ W₂ α βU β₁ β₂) : Function.Injective βU := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact hD.natU_ker


end Split


end CFSG.ASVolI

end
