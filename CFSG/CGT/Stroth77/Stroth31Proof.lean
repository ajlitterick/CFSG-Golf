module

public import CFSG.CGT.Stroth77.Stroth31
public import CFSG.GroupTheory.HuppertProduct.PGroupMho

public section

namespace CFSG.CGT.Stroth77

open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

noncomputable def fixedSubgroup (P Q : Type*) [Group P] [Group Q] [MulDistribMulAction P Q] :
    Subgroup Q where
  carrier := MulAction.fixedPoints P Q
  one_mem' := by
    rw [MulAction.mem_fixedPoints]
    intro p
    exact smul_one p
  mul_mem' := by
    intro x y hx hy
    rw [MulAction.mem_fixedPoints] at hx hy ⊢
    intro p
    rw [smul_mul', hx p, hy p]
  inv_mem' := by
    intro x hx
    rw [MulAction.mem_fixedPoints] at hx ⊢
    intro p
    rw [smul_inv', hx p]

@[simp]
theorem mem_fixedSubgroup {P Q : Type*} [Group P] [Group Q] [MulDistribMulAction P Q]
    {x : Q} : x ∈ fixedSubgroup P Q ↔ ∀ p : P, p • x = x :=
  Iff.rfl


@[expose]
noncomputable def conjOnSubgroupC {S : Type*} [Group S] {C : Subgroup S} (g : S)
    (hg : g ∈ Subgroup.normalizer C) : C →* C where
  toFun x := ⟨g * (x : S) * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg (x : S)).mp x.2⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Subgroup.coe_mk, Subgroup.coe_mul]
    group


@[expose]
noncomputable def conjQuotientMapC {S : Type*} [Group S] {B C : Subgroup S}
    [hN : (B.subgroupOf C).Normal] (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) :
    (C ⧸ B.subgroupOf C) →* (C ⧸ B.subgroupOf C) :=
  QuotientGroup.map (B.subgroupOf C) (B.subgroupOf C) (conjOnSubgroupC g hgC) (by
    intro x hx
    change g * (x : S) * g⁻¹ ∈ B
    exact (Subgroup.mem_normalizer_iff.mp hgB (x : S)).mp (Subgroup.mem_subgroupOf.mp hx))

@[simp]
theorem conjQuotientMapC_mk {S : Type*} [Group S] {B C : Subgroup S}
    [hN : (B.subgroupOf C).Normal] (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (x : C) :
    conjQuotientMapC g hgC hgB (QuotientGroup.mk x) =
      QuotientGroup.mk (conjOnSubgroupC g hgC x) := by
  rw [conjQuotientMapC]
  exact QuotientGroup.map_mk _ _ _ _ x

theorem conjQuotientMapC_left_inv {S : Type*} [Group S] {B C : Subgroup S}
    [hN : (B.subgroupOf C).Normal] (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) :
    Function.LeftInverse
      (conjQuotientMapC g⁻¹ (Subgroup.inv_mem _ hgC) (Subgroup.inv_mem _ hgB))
      (conjQuotientMapC g hgC hgB) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [conjQuotientMapC_mk, conjQuotientMapC_mk]
    congr 1
    ext
    simp only [conjOnSubgroupC, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mk]
    group

theorem conjQuotientMapC_right_inv {S : Type*} [Group S] {B C : Subgroup S}
    [hN : (B.subgroupOf C).Normal] (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) :
    Function.RightInverse
      (conjQuotientMapC g⁻¹ (Subgroup.inv_mem _ hgC) (Subgroup.inv_mem _ hgB))
      (conjQuotientMapC g hgC hgB) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [conjQuotientMapC_mk, conjQuotientMapC_mk]
    congr 1
    ext
    simp only [conjOnSubgroupC, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mk]
    group

@[expose]
noncomputable def conjAutQuotientC {S : Type*} [Group S] {B C : Subgroup S}
    [hN : (B.subgroupOf C).Normal] (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) : MulAut (C ⧸ B.subgroupOf C) :=
  MulEquiv.ofBijective (conjQuotientMapC g hgC hgB)
    ⟨(conjQuotientMapC_left_inv g hgC hgB).injective,
     (conjQuotientMapC_right_inv g hgC hgB).surjective⟩

@[simp]
theorem conjAutQuotientC_apply_mk {S : Type*} [Group S] {B C : Subgroup S}
    [hN : (B.subgroupOf C).Normal] (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (x : C) :
    conjAutQuotientC g hgC hgB (QuotientGroup.mk x) =
      QuotientGroup.mk (conjOnSubgroupC g hgC x) :=
  conjQuotientMapC_mk g hgC hgB x


end CFSG.CGT.Stroth77
