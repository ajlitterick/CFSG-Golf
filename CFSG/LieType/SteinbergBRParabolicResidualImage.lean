module

public import CFSG.LieType.SteinbergBRParabolicTransport
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex

public section

namespace CFSG.LieType.SteinbergBR.BlockPar

open Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type*} [Field F] {n d e : ℕ}

@[expose] noncomputable def parQEquiv (h : d + e = n) {s : SpecialLinearGroup (Fin n) F}
    {W : Submodule F (Fin n → F)} (hs : (flagSpace n F d).map (mulVecLin s.val) = W) :
    (parQ : Subgroup (SpecialLinearGroup (Fin d ⊕ Fin e) F)) ≃* stabilizer W :=
  ((transportSL F h s).subgroupMap parQ).trans
    (MulEquiv.subgroupCongr (map_parQ_transport h hs))

theorem perfectResidual_stabilizer_eq (h : d + e = n) {s : SpecialLinearGroup (Fin n) F}
    {W : Submodule F (Fin n → F)} (hs : (flagSpace n F d).map (mulVecLin s.val) = W)
    {K : Subgroup (SpecialLinearGroup (Fin d ⊕ Fin e) F)} (hK : K ≤ parQ)
    (hres : CFSG.perfectResidual (parQ : Subgroup (SpecialLinearGroup (Fin d ⊕ Fin e) F)) =
      K.subgroupOf parQ) :
    (CFSG.perfectResidual (stabilizer W)).map (stabilizer W).subtype =
      K.map (transportSL F h s).toMonoidHom := by
  rw [← perfectResidual_map_equiv (parQEquiv h hs), hres, Subgroup.map_map]
  have hcomp : (stabilizer W).subtype.comp (parQEquiv h hs).toMonoidHom =
      (transportSL F h s).toMonoidHom.comp parQ.subtype :=
    MonoidHom.ext fun _ => rfl
  rw [hcomp, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left hK]

theorem val_eq_scalar_of_transport (h : d + e = n) (s : SpecialLinearGroup (Fin n) F)
    {k : SpecialLinearGroup (Fin d ⊕ Fin e) F} {c : F}
    (hc : (transportSL F h s k).val = scalar (Fin n) c) :
    k.val = scalar (Fin d ⊕ Fin e) c := by
  have h1 := transportSL_symm_scalar h s hc
  rwa [MulEquiv.symm_apply_apply] at h1

theorem map_inf_scalars_eq_bot_left [NeZero d] (h : d + e = n) (s : SpecialLinearGroup (Fin n) F)
    {K : Subgroup (SpecialLinearGroup (Fin d ⊕ Fin e) F)}
    (hK : ∀ g ∈ K, g.val.toBlocks₁₁ = 1) :
    K.map (transportSL F h s).toMonoidHom ⊓ scalars n F = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨k, hk, rfl⟩, c, -, hc⟩
  have hk' := val_eq_scalar_of_transport h s hc
  have h11 := congrFun₂ (hK k hk) 0 0
  change k.val (Sum.inl 0) (Sum.inl 0) = (1 : Matrix (Fin d) (Fin d) F) 0 0 at h11
  rw [one_apply_eq, hk', scalar_apply, diagonal_apply_eq] at h11
  have hk1 : k = 1 := Subtype.ext (by rw [hk', h11, map_one]; rfl)
  rw [Subgroup.mem_bot, hk1, map_one]

theorem map_inf_scalars_eq_bot_right [NeZero e] (h : d + e = n) (s : SpecialLinearGroup (Fin n) F)
    {K : Subgroup (SpecialLinearGroup (Fin d ⊕ Fin e) F)}
    (hK : ∀ g ∈ K, g.val.toBlocks₂₂ = 1) :
    K.map (transportSL F h s).toMonoidHom ⊓ scalars n F = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨k, hk, rfl⟩, c, -, hc⟩
  have hk' := val_eq_scalar_of_transport h s hc
  have h22 := congrFun₂ (hK k hk) 0 0
  change k.val (Sum.inr 0) (Sum.inr 0) = (1 : Matrix (Fin e) (Fin e) F) 0 0 at h22
  rw [one_apply_eq, hk', scalar_apply, diagonal_apply_eq] at h22
  have hk1 : k = 1 := Subtype.ext (by rw [hk', h22, map_one]; rfl)
  rw [Subgroup.mem_bot, hk1, map_one]

theorem injOn_mk_of_inf_eq_bot {G : Type*} [Group G] {D J : Subgroup G} [D.Normal]
    (h : J ⊓ D = ⊥) : Set.InjOn (QuotientGroup.mk' D) (J : Set G) := by
  intro x hx y hy hxy
  have hD : x⁻¹ * y ∈ D := QuotientGroup.eq.1 hxy
  have hmem : x⁻¹ * y ∈ J ⊓ D := ⟨J.mul_mem (J.inv_mem hx) hy, hD⟩
  rw [h, Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.1 hmem

theorem perfectResidual_map_subtype_congr {A : Type*} [Group A] {X Y : Subgroup A}
    (h : X = Y) :
    (CFSG.perfectResidual X).map X.subtype = (CFSG.perfectResidual Y).map Y.subtype := by
  subst h
  rfl

theorem map_perfectResidual_subgroup {G A : Type*} [Group G] [Group A] [Finite G] [Finite A]
    (π : G →* A) (Q : Subgroup G) :
    ((CFSG.perfectResidual Q).map Q.subtype).map π =
      (CFSG.perfectResidual (Q.map π)).map (Q.map π).subtype := by
  obtain ⟨h, -, -⟩ := CFSG.perfect_residual_transport (π.comp Q.subtype)
  rw [Subgroup.map_map, h]
  exact perfectResidual_map_subtype_congr (by rw [MonoidHom.range_comp, Subgroup.range_subtype])


end CFSG.LieType.SteinbergBR.BlockPar
