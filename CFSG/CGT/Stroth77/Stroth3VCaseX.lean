module

public import CFSG.CGT.Stroth77.Stroth3VCase
public import CFSG.CGT.Stroth77.Stroth39

public section

namespace CFSG.CGT.Stroth77

open CFSG.OddStandard.HigherRank.G2Three.Sec1 (IsSylowIn)


namespace StrothWeakTypeData

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {τ : StrothTypeIndex}
  (dD : StrothWeakTypeData D τ)


theorem eq_of_inv_mul_mem (hk : 1 ≤ τ.k 0) {x y : G} (hx : x ∈ Subgroup.normalizer (D : Set G))
    (hy : y ∈ Subgroup.normalizer (D : Set G)) {a b : Torus τ.k} (ha : InW a) (hb : InW b)
    (hθx : ∀ v, dD.thetaT hx v = nuMap a v) (hθy : ∀ v, dD.thetaT hy v = nuMap b v)
    (hxy : x⁻¹ * y ∈ D) : a = b := by
  have key : ∀ v, nuMap (b + a) v = nuMap 0 v := fun v => by
    rw [nuMap_zero, ← nuMap_nuMap ha.1, ← hθy, ← dD.thetaT_inv_of_nu hx ha hθx,
      ← dD.thetaT_mul (inv_mem hx) hy]
    exact dD.thetaT_of_mem _ hxy v
  have := nuMap_injective hk key
  rw [add_eq_zero_iff_eq_neg] at this
  rw [this, neg_eq_of_add_eq_zero_left ha.2]

theorem conj_eq_iff_even {g : G} (hg : g ∈ Subgroup.normalizer (D : Set G)) {v : Torus τ.k}
    (hv : InW v) (hv0 : v ≠ 0) (hθ : ∀ x, dD.thetaT hg x = nuMap v x) {d : G} (hd : d ∈ D) :
    g⁻¹ * d * g = d ↔ (crdT dD.e d 0).val % 2 = 0 := by
  have hd' := (Subgroup.mem_normalizer_iff''.mp hg d).mp hd
  rw [← nuMap_eq_self_iff hv.2 hv0, ← hθ, dD.thetaT_crdT hg hd]
  exact ⟨fun h => by rw [h], fun h => crdT_inj dD.e hd' hd h⟩

theorem mul_comm_iff_conj {g x : G} : x * g = g * x ↔ g⁻¹ * x * g = x := by
  constructor
  · intro h; rw [mul_assoc, h, inv_mul_cancel_left]
  · intro h
    calc x * g = g * (g⁻¹ * x * g) := by group
      _ = g * x := by rw [h]

end StrothWeakTypeData

namespace StrothFrame.IsD


end StrothFrame.IsD

end CFSG.CGT.Stroth77
