module

public import CFSG.CGT.Stroth77.Extension22FourBasis

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] {B C : Subgroup S} {m : ℕ}

@[expose] noncomputable def basisElemsFour (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (e f : C) : Fin 3 → C :=
  ![⟨D.c, hBC D.c.2⟩, e, f]

@[simp]
theorem basisElemsFour_zero (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (e f : C) :
    basisElemsFour D hBC e f 0 = ⟨D.c, hBC D.c.2⟩ := rfl

@[simp]
theorem basisElemsFour_one (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (e f : C) :
    basisElemsFour D hBC e f 1 = e := rfl

@[simp]
theorem basisElemsFour_two (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (e f : C) :
    basisElemsFour D hBC e f 2 = f := rfl

@[expose] noncomputable def TorusBasisEquivFour.symm
    {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}
    (E : TorusBasisEquivFour D hBC e f) : Additive C ≃+ Torus (Type200.k m) :=
  E.E.symm

theorem TorusBasisEquivFour.symm_gen_zero
    {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}
    (E : TorusBasisEquivFour D hBC e f) :
    E.symm (Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C)) = gen (Type200.k m) 0 := by
  show E.E.symm (Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C)) = gen (Type200.k m) 0
  rw [← E.E_gen0]
  exact E.E.symm_apply_apply _

theorem TorusBasisEquivFour.symm_gen_one
    {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}
    (E : TorusBasisEquivFour D hBC e f) :
    E.symm (Additive.ofMul e) = gen (Type200.k m) 1 := by
  show E.E.symm (Additive.ofMul e) = gen (Type200.k m) 1
  rw [← E.E_gen1]
  exact E.E.symm_apply_apply _

theorem TorusBasisEquivFour.symm_gen_two
    {D : StrothTypeData B (StrothTypeIndex.t100 m)} {hBC : B ≤ C} {e f : C}
    (E : TorusBasisEquivFour D hBC e f) :
    E.symm (Additive.ofMul f) = gen (Type200.k m) 2 := by
  show E.E.symm (Additive.ofMul f) = gen (Type200.k m) 2
  rw [← E.E_gen2]
  exact E.E.symm_apply_apply _

structure HasGeneratorImagesFour (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hL : D.L ≤ Subgroup.normalizer C) (e f : C)
    {k : Fin 3 → ℕ} (E : Additive C ≃+ Torus k)
    (φuv φt φu φρ : Torus k →+ Torus k) : Prop where
  uv : ∀ j : Fin 3,
    E (Additive.ofMul (conjBy (hL D.uv_mem_L) (basisElemsFour D hBC e f j))) =
      φuv (gen k j)
  t : ∀ j : Fin 3,
    E (Additive.ofMul (conjBy (hL D.t_mem_L) (basisElemsFour D hBC e f j))) =
      φt (gen k j)
  u : ∀ j : Fin 3,
    E (Additive.ofMul (conjBy (hL D.u_mem_L) (basisElemsFour D hBC e f j))) =
      φu (gen k j)
  ρ : ∀ j : Fin 3,
    E (Additive.ofMul (conjBy (hL D.ρ_mem_L) (basisElemsFour D hBC e f j))) =
      φρ (gen k j)

@[expose] def Type200Images (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hL : D.L ≤ Subgroup.normalizer C) (e f : C)
    (E : TorusBasisEquivFour D hBC e f) : Prop :=
  HasGeneratorImagesFour D hBC hL e f (k := Type200.k m) E.symm
    (Type200.action m).φuv (Type200.action m).φt (Type200.action m).φu
    (Type200.action m).φρ

@[expose] def Type201Images (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hL : D.L ≤ Subgroup.normalizer C) (e f : C)
    (E : TorusBasisEquivFour D hBC e f) : Prop :=
  HasGeneratorImagesFour D hBC hL e f (k := Type201.k m)
    (show Additive C ≃+ Torus (Type201.k m) from E.symm)
    (Type201.action m).φuv (Type201.action m).φt (Type201.action m).φu
    (Type201.action m).φρ


@[expose] def HasType200Or201AdjustedBasis
    (D : StrothTypeData B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hL : D.L ≤ Subgroup.normalizer C) (e f : C)
    (he : e * e = ⟨D.a, hBC D.a.2⟩) (hf : f * f = ⟨D.b, hBC D.b.2⟩)
    (E : TorusBasisEquivFour D hBC e f) : Prop :=
  ∃ z w : C, z * z = 1 ∧ w * w = 1 ∧
    ∃ E' : TorusBasisEquivFour D hBC (e * z) (f * w),
      Type200Images D hBC hL (e * z) (f * w) E' ∨
        Type201Images D hBC hL (e * z) (f * w) E'


end CFSG.CGT.Stroth77
