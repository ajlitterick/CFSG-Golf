module

public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang
import CFSG.GroupTheory.NormalOddInversion

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups
open Subgroup CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley


theorem mem_closedIdentityComponent_of_order_three_of_inverted
    {τ : Tag} {k : Type} [Field k]
    (Z : Subgroup (ModGL τ k)) (g e : ModGL τ k)
    (hg : g ∈ closedIdentityComponent Z) (heZ : e ∈ Z)
    (he : e ^ 3 = 1) (hinv : g * e * g⁻¹ = e⁻¹) :
    e ∈ closedIdentityComponent Z := by
  let g0 : Z := ⟨g, closedIdentityComponent_le Z hg⟩
  let e0 : Z := ⟨e, heZ⟩
  have he0 : e0 ^ 3 = 1 := Subtype.ext he
  have hg0 : g0 ∈ (closedIdentityComponent Z).subgroupOf Z := hg
  have hinv0 : g0 * e0 * g0⁻¹ = e0⁻¹ := Subtype.ext hinv
  have hm := CFSG.GroupTheory.mem_of_normal_of_odd_pow_eq_one_of_conj_eq_inv hg0
    (by decide : Odd (3 : ℕ)) he0 hinv0
  exact hm


end CFSG.LieType.AlgebraicGroups
