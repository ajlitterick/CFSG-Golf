module

public import CFSG.LieType.Chevalley.TwistMap
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

variable (t : TwistTag) (K : Type) [Field K] (σ : K →+* K)

theorem twistedFixedGroup_le_adjointGroup : twistedFixedGroup t K σ ≤ adjointGroup t.tag K :=
  inf_le_left

theorem coe_mem_twistedFixedGroup_iff (g : adjointGroup t.tag K) :
    (g : ModGL t.tag K) ∈ twistedFixedGroup t K σ ↔ twistC t K σ g = g :=
  ⟨fun h => Subtype.ext h.2, fun h => ⟨g.2, congrArg Subtype.val h⟩⟩

theorem mem_twistedFixedGroup_iff {g : ModGL t.tag K} :
    g ∈ twistedFixedGroup t K σ ↔
      ∃ x : adjointGroup t.tag K, twistC t K σ x = x ∧ (x : ModGL t.tag K) = g :=
  ⟨fun h => ⟨⟨g, h.1⟩, (coe_mem_twistedFixedGroup_iff t K σ ⟨g, h.1⟩).1 h, rfl⟩,
    fun ⟨x, hx, hxg⟩ => hxg ▸ (coe_mem_twistedFixedGroup_iff t K σ x).2 hx⟩

theorem twistedFixedGroup_eq_map :
    twistedFixedGroup t K σ =
      (MonoidHom.eqLocus (twistC t K σ) (MonoidHom.id _)).map (adjointGroup t.tag K).subtype := by
  ext g
  rw [mem_twistedFixedGroup_iff]
  exact ⟨fun ⟨x, hx, hxg⟩ => ⟨x, hx, hxg⟩, fun ⟨x, hx, hxg⟩ => ⟨x, hx, hxg⟩⟩

theorem twistedFixedGroup_subgroupOf :
    (twistedFixedGroup t K σ).subgroupOf (adjointGroup t.tag K) =
      MonoidHom.eqLocus (twistC t K σ) (MonoidHom.id _) := by
  ext g
  rw [Subgroup.mem_subgroupOf, coe_mem_twistedFixedGroup_iff]
  rfl

@[expose] noncomputable def twistedFixedGroupEquiv :
    twistedFixedGroup t K σ ≃* MonoidHom.eqLocus (twistC t K σ) (MonoidHom.id _) :=
  ((Subgroup.equivMapOfInjective _ (adjointGroup t.tag K).subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr (twistedFixedGroup_eq_map t K σ).symm)).symm


end CFSG.LieType.Chevalley
