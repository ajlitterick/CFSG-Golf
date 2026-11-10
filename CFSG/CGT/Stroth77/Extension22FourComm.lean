module

public import CFSG.CGT.Stroth77.Extension22FourProof

public section

namespace CFSG

open scoped commutatorElement

theorem isMulCommutative_of_forall_mul_self {G : Type*} [Group G]
    (h : ∀ x : G, x * x = 1) : IsMulCommutative G := by
  refine ⟨⟨fun x y => ?_⟩⟩
  have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (h x)
  have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right (h y)
  have hxy : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (h (x * y))
  calc
    x * y = (x * y)⁻¹ := hxy.symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hx, hy]

def commutatorFiberLeft {G : Type*} [Group G] (N : Subgroup G) [hN : N.Normal] (a : G) :
    Subgroup G where
  carrier := {x | ⁅a, x⁆ ∈ N}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    change ⁅a, x * y⁆ ∈ N
    rw [commutatorElement_mul_right_eq_mul_conj]
    rw [show ⁅a, x⁆ * x * ⁅a, y⁆ * x⁻¹ = ⁅a, x⁆ * (x * ⁅a, y⁆ * x⁻¹) by group]
    exact N.mul_mem hx (hN.conj_mem _ hy x)
  inv_mem' := by
    intro x hx
    change ⁅a, x⁻¹⁆ ∈ N
    rw [commutatorElement_inv_right]
    simpa using hN.conj_mem _ (by simpa [commutatorElement_inv] using N.inv_mem hx) x⁻¹

@[simp]
theorem mem_commutatorFiberLeft {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    {a x : G} : x ∈ commutatorFiberLeft N a ↔ ⁅a, x⁆ ∈ N := Iff.rfl

def commutatorCentralizer {G : Type*} [Group G] (N : Subgroup G) [hN : N.Normal] :
    Subgroup G where
  carrier := {x | ∀ y : G, ⁅x, y⁆ ∈ N}
  one_mem' := by intro y; simp
  mul_mem' := by
    intro x y hx hy z
    change ⁅x * y, z⁆ ∈ N
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact N.mul_mem (hN.conj_mem _ (hy z) x) (hx z)
  inv_mem' := by
    intro x hx y
    change ⁅x⁻¹, y⁆ ∈ N
    rw [commutatorElement_inv_left]
    simpa using hN.conj_mem _ (by simpa [commutatorElement_inv] using N.inv_mem (hx y)) x⁻¹

@[simp]
theorem mem_commutatorCentralizer {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    {x : G} : x ∈ commutatorCentralizer N ↔ ∀ y : G, ⁅x, y⁆ ∈ N := Iff.rfl

theorem eq_top_of_le_of_map_quotient_eq_top {G : Type*} [Group G] {N K : Subgroup G}
    [N.Normal] (hNK : N ≤ K) (hmap : K.map (QuotientGroup.mk' N) = ⊤) : K = ⊤ := by
  refine eq_top_iff.mpr fun x _ => ?_
  have hx : QuotientGroup.mk' N x ∈ K.map (QuotientGroup.mk' N) := by
    rw [hmap]
    exact Subgroup.mem_top _
  obtain ⟨k, hkK, hkx⟩ := Subgroup.mem_map.mp hx
  have hmem : k⁻¹ * x ∈ N := by
    have h1 : QuotientGroup.mk' N (k⁻¹ * x) = 1 := by
      rw [map_mul, map_inv, hkx, inv_mul_cancel]
    exact (QuotientGroup.eq_one_iff (N := N) (k⁻¹ * x)).mp (by simpa using h1)
  have hxK : x ∈ K := by
    have hx_eq : x = k * (k⁻¹ * x) := by group
    rw [hx_eq]
    exact K.mul_mem hkK (hNK hmem)
  exact hxK

end CFSG

namespace CFSG.CGT.Stroth77

open scoped commutatorElement

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S} {m : ℕ}


@[expose]
noncomputable def conjAutOfMemNormalizer (g : S) (hg : g ∈ Subgroup.normalizer C) : MulAut C where
  toFun x := ⟨g * (x : S) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (x : S)).mp x.2⟩
  invFun x := ⟨g⁻¹ * (x : S) * g, (Subgroup.mem_normalizer_iff''.mp hg (x : S)).mp x.2⟩
  left_inv x := by
    apply Subtype.ext
    simp only [Subgroup.coe_mk]
    group
  right_inv x := by
    apply Subtype.ext
    simp only [Subgroup.coe_mk]
    group
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mk, Subgroup.coe_mul]
    group

@[simp]
theorem conjAutOfMemNormalizer_apply (g : S) (hg : g ∈ Subgroup.normalizer C) (x : C) :
    (conjAutOfMemNormalizer g hg x : S) = g * (x : S) * g⁻¹ := rfl


end CFSG.CGT.Stroth77
