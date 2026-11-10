module

public import CFSG.Quasithin.AppendixH.H11.NativeBridge
public import CFSG.Quasithin.AppendixH.H11.NativeVectors
public import CFSG.Quasithin.AppendixH.H11.ModuleRank
public import CFSG.Quasithin.Background.SzG11M12Syl

public section

namespace CFSG.Quasithin.AppendixH.H11

open CFSG.Quasithin
open scoped IsMulCommutative

namespace NativeCoords

variable {V : Type*} [CommGroup V] {L : Subgroup (MulAut V)} (c : NativeCoords L)

private theorem mem_zpowers_of_mk_eq {m m' : G6.coreMod 12}
    (h : (QuotientGroup.mk m : Q12) = QuotientGroup.mk m') :
    ((m : G6.PermMod 12) * (m' : G6.PermMod 12)⁻¹) ∈ Subgroup.zpowers (G6.allOnes 12) := by
  have hN : m * m'⁻¹ ∈ (Subgroup.zpowers (G6.allOnes 12)).subgroupOf (G6.coreMod 12) := by
    rw [← QuotientGroup.eq_one_iff]
    change (QuotientGroup.mk m * (QuotientGroup.mk m')⁻¹ : Q12) = 1
    rw [h, mul_inv_cancel]
  have hperm := Subgroup.mem_subgroupOf.mp hN
  rw [Subgroup.coe_mul, Subgroup.coe_inv] at hperm
  exact hperm


theorem injective : Function.Injective c.π := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  apply Subtype.ext
  apply eq_one_of_mem_zpowers_allOnes
  intro x hx
  let v : V := c.ψ.symm (QuotientGroup.mk (⟨x, hx⟩ : G6.coreMod 12))
  have hm : c.ψ v = QuotientGroup.mk (⟨x, hx⟩ : G6.coreMod 12) := by
    simp [v]
  have heq := c.equivariant γ v ⟨x, hx⟩ hm
  have hcoe : ((c.π γ : ↥L) : MulAut V) = 1 := by rw [hγ]; rfl
  have hmk : (QuotientGroup.mk (G6.coreAct 12 (γ : Equiv.Perm (Fin 12)) ⟨x, hx⟩) : Q12) =
      QuotientGroup.mk (⟨x, hx⟩ : G6.coreMod 12) := by
    simpa [hcoe, hm] using heq.symm
  have hmem := mem_zpowers_of_mk_eq hmk
  simpa [G6.coreAct_coe] using hmem


end NativeCoords

end CFSG.Quasithin.AppendixH.H11
