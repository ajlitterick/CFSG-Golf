module


public import CFSG.Monster.B.TwoA.Sp8.SubgeomVec
public import CFSG.Monster.B.TwoA.Sp8.SubgeomData

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open Module Submodule CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

attribute [local instance] parAction

theorem obj_le_A8
    {x : ParGeom} (hx : x ∈ subgeom) : x.1.2 ≤ A8 := by
  obtain ⟨h4, h, hh, hxh⟩ := mem_subgeom.1 hx
  rw [hxh]
  exact conjSub_le_A8 hh (Echain_le_A8 (parType_bounds x).1 h4)

theorem isotropic_obj
    {x : ParGeom} (hx : x ∈ subgeom) :
    IsTotallyIsotropic b0 (a8Vec x.1.2) ∧ finrank (ZMod 2) (a8Vec x.1.2) = parType x := by
  obtain ⟨h4, h, hh, hxh⟩ := mem_subgeom.1 hx
  rw [hxh]
  exact isotropic_a8Vec_conjSub ⟨h, hh⟩ (parType_bounds x).1 h4

theorem eq_of_a8Vec_eq
    {x y : ParGeom} (hx : x ∈ subgeom) (hy : y ∈ subgeom)
    (h : a8Vec x.1.2 = a8Vec y.1.2) : x = y := by
  have ht : parType x = parType y := by
    rw [← (isotropic_obj hx).2, ← (isotropic_obj hy).2, h]
  exact Subtype.ext (Prod.ext ht (a8Vec_injective (obj_le_A8 hx) (obj_le_A8 hy) h))

@[expose] def xToS :
    Xgrp →* Shat := Subgroup.inclusion Xgrp_le_Shat


theorem a8Vec_smul
    (x : Xgrp) {c : ParGeom} (hc : c ∈ subgeom) :
    a8Vec (xToS x • c).1.2 = (a8Vec c.1.2).map (rhoX x : V8 →ₗ[ZMod 2] V8) :=
  a8Vec_conjSub x (obj_le_A8 hc)

@[expose, instance_reducible] def subgeomAction :
    MulAction Xgrp subgeom where
  smul x c := ⟨xToS x • c.1, smul_mem_subgeom x.2 c.2⟩
  one_smul c := Subtype.ext (by
    show xToS 1 • c.1 = c.1
    rw [map_one, one_smul])
  mul_smul x y c := Subtype.ext (by
    show xToS (x * y) • c.1 = xToS x • xToS y • c.1
    rw [map_mul, mul_smul])


attribute [local instance] subgeomAction

attribute [local instance] subgeomAction


theorem smul_eq_self_iff
    (x : Xgrp) {c : ParGeom} (hc : c ∈ subgeom) :
    xToS x • c = c ↔ (a8Vec c.1.2).map (rhoX x : V8 →ₗ[ZMod 2] V8) = a8Vec c.1.2 := by
  constructor
  · intro h
    rw [← a8Vec_smul x hc, h]
  · intro h
    exact eq_of_a8Vec_eq (smul_mem_subgeom x.2 hc) hc ((a8Vec_smul x hc).trans h)


theorem pair_one_mem
    {a : Dfull} (ha : a ∈ A8) (ha1 : a ≠ 1) :
    (1, Subgroup.zpowers a) ∈ subgeomPairs := by
  obtain ⟨h, hh, hha⟩ := Xgrp_transitive xhat_mem_A8_e0 ha TwoA.xhat_ne_one ha1
  refine ⟨le_rfl, by norm_num, h, hh, ?_⟩
  show Subgroup.zpowers a = conjSub h (Subgroup.zpowers xhat)
  rw [conjSub, MonoidHom.map_zpowers, ← hha]
  rfl

theorem pair_le_A8
    {p : ℕ × Subgroup Dfull} (hp : p ∈ subgeomPairs) : p.2 ≤ A8 :=
  obj_le_A8 (x := ⟨p, subgeomPairs_subset_ParObj hp⟩) hp


theorem stab_D_iff
    (d : Dfull) :
    (fun p : ℕ × Subgroup Dfull => (p.1, conjSub d p.2)) '' subgeomPairs = subgeomPairs ↔
      d ∈ Xgrp := by
  constructor
  · intro h
    rw [← normalizer_A8_eq]
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    by_cases ha1 : a = 1
    · rw [ha1, mul_one, mul_inv_cancel]
      exact A8.one_mem
    have hp : (1, conjSub d (Subgroup.zpowers a)) ∈ subgeomPairs := by
      rw [← h]
      exact ⟨_, pair_one_mem ha ha1, rfl⟩
    exact pair_le_A8 hp (conj_mem_conjSub (Subgroup.mem_zpowers a))
  · intro hd
    ext p
    constructor
    · rintro ⟨q, ⟨h1, h4, k, hk, e⟩, rfl⟩
      refine ⟨h1, h4, d * k, Xgrp.mul_mem hd hk, ?_⟩
      show conjSub d q.2 = conjSub (d * k) (Echain q.1)
      rw [e, conjSub_mul]
    · rintro ⟨h1, h4, k, hk, e⟩
      refine ⟨(p.1, conjSub d⁻¹ p.2), ⟨h1, h4, d⁻¹ * k, Xgrp.mul_mem (Xgrp.inv_mem hd) hk, ?_⟩, ?_⟩
      · show conjSub d⁻¹ p.2 = conjSub (d⁻¹ * k) (Echain p.1)
        rw [e, conjSub_mul]
      · show (p.1, conjSub d (conjSub d⁻¹ p.2)) = p
        rw [conjSub_conjSub_inv]

theorem stab_S_iff
    (s : Shat) : (s • ·) '' subgeom = subgeom ↔ (s : Dfull) ∈ Xgrp := by
  refine ⟨fun h => (stab_D_iff s).1 ?_, fun h => subgeomConj_of_mem h⟩
  rw [← image_val_subgeom, Set.image_image]
  conv_rhs => rw [← h]
  rw [Set.image_image]
  rfl

end CFSG.Monster.B.TwoA.Sp8
