module

public import CFSG.ClassicalInvolution.Asc77.WP2Thm6
public import CFSG.ClassicalInvolution.AschTight.E3StarD

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.GorensteinWalter
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G]


theorem centralizerModOdd_le_cStar (H K : Subgroup G) : centralizerModOdd H K ≤ cStar K := by
  rintro x ⟨-, hxN, -, hx⟩
  refine mem_cStar_iff.mpr ⟨hxN, fun k => ?_⟩
  obtain ⟨o, ho, hoe⟩ := Subgroup.mem_map.mp (hx ((k : G)⁻¹) (K.inv_mem k.2))
  have hoe' : (o : G) = ⁅x, (k : G)⁻¹⁆ := hoe
  have e : (normalizerConj K ⟨x, hxN⟩ k)⁻¹ * k = o := by
    apply Subtype.ext
    rw [hoe', Subgroup.coe_mul, Subgroup.coe_inv, normalizerConj_apply_coe,
      commutatorElement_def]
    group
  rw [e]
  exact ho

theorem xGroup_eq_gammaGen (K : Subgroup G) (z : G) :
    xGroup K z = gammaGen (CoreAssembly.conjClass K) z := by
  simp only [xGroup, gammaGen, or_comm]


end CFSG.ClassicalInvolution.Disconnected.AschTight
