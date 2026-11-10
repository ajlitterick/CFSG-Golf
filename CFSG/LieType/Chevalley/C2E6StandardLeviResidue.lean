module

public import CFSG.LieType.Chevalley.C2E6StandardBetaStar
public import CFSG.LieType.Chevalley.C2E6StandardLeviFactors

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
open scoped Pointwise

variable {J : Set (Fin 4)}

abbrev radicalOf
    (J : Set (Fin 4)) : Subgroup (nativeParabolic J) :=
  (stdRadical J).subgroupOf (nativeParabolic J)

instance
    (J : Set (Fin 4)) : (radicalOf J).Normal := stdRadical_normal J

@[expose] def leviToQuot
    (hJ : (2 : Fin 4) ∈ J) : stdLevi J →* nativeParabolic J ⧸ radicalOf J :=
  (QuotientGroup.mk' (radicalOf J)).comp (Subgroup.inclusion (stdLevi_le_nativeParabolic hJ))

theorem leviToQuot_apply
    (hJ : (2 : Fin 4) ∈ J) (l : stdLevi J) :
    leviToQuot hJ l = QuotientGroup.mk (Subgroup.inclusion (stdLevi_le_nativeParabolic hJ) l) :=
  rfl

theorem leviToQuot_bijective
    (hJ : (2 : Fin 4) ∈ J) : Function.Bijective (leviToQuot hJ) := by
  constructor
  · rw [injective_iff_map_eq_one]
    intro l hl
    rw [leviToQuot_apply, QuotientGroup.eq_one_iff] at hl
    have h1 : (l : ModGL Tag.E6 K) ∈ stdRadical J ⊓ stdLevi J := Subgroup.mem_inf.mpr ⟨hl, l.2⟩
    rw [stdRadical_inf_stdLevi] at h1
    exact Subtype.ext h1
  · intro x
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨⟨q, l⟩, ⟨hq, hl, hpql⟩, -⟩ := existsUnique_stdRadical_mul_stdLevi hJ p.2
    refine ⟨⟨l, hl⟩, ?_⟩
    have hp : p = (⟨q, stdRadical_le_nativeParabolic J hq⟩ : nativeParabolic J) *
        ⟨l, stdLevi_le_nativeParabolic hJ hl⟩ := Subtype.ext hpql
    rw [hp, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr
      (show (⟨q, stdRadical_le_nativeParabolic J hq⟩ : nativeParabolic J) ∈ radicalOf J from hq),
      one_mul]
    rfl

@[expose] def leviProj
    (hJ : (2 : Fin 4) ∈ J) : nativeParabolic J →* stdLevi J :=
  (MulEquiv.ofBijective _ (leviToQuot_bijective hJ)).symm.toMonoidHom.comp
    (QuotientGroup.mk' (radicalOf J))

theorem leviToQuot_leviProj
    (hJ : (2 : Fin 4) ∈ J) (p : nativeParabolic J) :
    leviToQuot hJ (leviProj hJ p) = QuotientGroup.mk p :=
  (MulEquiv.ofBijective _ (leviToQuot_bijective hJ)).apply_symm_apply _

theorem leviProj_mul
    (hJ : (2 : Fin 4) ∈ J) {q l : ModGL Tag.E6 K} (hq : q ∈ stdRadical J)
    (hl : l ∈ stdLevi J) (hql : q * l ∈ nativeParabolic J) :
    leviProj hJ ⟨q * l, hql⟩ = ⟨l, hl⟩ := by
  apply (leviToQuot_bijective hJ).1
  rw [leviToQuot_leviProj, leviToQuot_apply]
  have hp : (⟨q * l, hql⟩ : nativeParabolic J) =
      (⟨q, stdRadical_le_nativeParabolic J hq⟩ : nativeParabolic J) *
        ⟨l, stdLevi_le_nativeParabolic hJ hl⟩ := rfl
  rw [hp, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr
    (show (⟨q, stdRadical_le_nativeParabolic J hq⟩ : nativeParabolic J) ∈ radicalOf J from hq),
    one_mul]
  rfl

theorem leviProj_of_mem
    (hJ : (2 : Fin 4) ∈ J) {l : ModGL Tag.E6 K} (hl : l ∈ stdLevi J)
    (hlP : l ∈ nativeParabolic J) : leviProj hJ ⟨l, hlP⟩ = ⟨l, hl⟩ := by
  have h := leviProj_mul hJ (one_mem _) hl (by rw [one_mul]; exact hlP)
  simp only [one_mul] at h
  exact h

theorem mul_inv_leviProj_mem
    (hJ : (2 : Fin 4) ∈ J) (p : nativeParabolic J) :
    (p : ModGL Tag.E6 K) * ((leviProj hJ p : stdLevi J) : ModGL Tag.E6 K)⁻¹ ∈ stdRadical J := by
  set l := leviProj hJ p
  have hlP : (l : ModGL Tag.E6 K) ∈ nativeParabolic J := stdLevi_le_nativeParabolic hJ l.2
  have h1 : leviProj hJ (p * (⟨l, hlP⟩ : nativeParabolic J)⁻¹) = 1 := by
    rw [map_mul, map_inv, leviProj_of_mem hJ l.2 hlP]
    exact mul_inv_cancel l
  have h2 := leviToQuot_leviProj hJ (p * (⟨l, hlP⟩ : nativeParabolic J)⁻¹)
  rw [h1, map_one] at h2
  have h3 : p * (⟨l, hlP⟩ : nativeParabolic J)⁻¹ ∈ radicalOf J :=
    (QuotientGroup.eq_one_iff _).mp h2.symm
  exact h3

theorem leviProj_eq_one_iff
    (hJ : (2 : Fin 4) ∈ J) (p : nativeParabolic J) :
    leviProj hJ p = 1 ↔ (p : ModGL Tag.E6 K) ∈ stdRadical J := by
  constructor
  · intro h
    have := mul_inv_leviProj_mem hJ p
    rwa [h, OneMemClass.coe_one, inv_one, mul_one] at this
  · intro hp
    have e : p = ⟨(p : ModGL Tag.E6 K) * 1, by rw [mul_one]; exact p.2⟩ :=
      Subtype.ext (mul_one _).symm
    rw [e, leviProj_mul hJ hp (one_mem _)]
    rfl

theorem leviProj_mem_stdLeviBorel
    (hJ : (2 : Fin 4) ∈ J) {b : nativeParabolic J}
    (hb : (b : ModGL Tag.E6 K) ∈ stdBorel) :
    ((leviProj hJ b : stdLevi J) : ModGL Tag.E6 K) ∈ stdLeviBorel J := by
  obtain ⟨⟨q, c⟩, ⟨hq, hc, hbqc⟩, -⟩ := existsUnique_stdRadical_mul_stdBorel J hb
  have e : b = ⟨q * c, hbqc ▸ b.2⟩ := Subtype.ext hbqc
  rw [e, leviProj_mul hJ hq (stdLeviBorel_le_stdLevi hJ hc)]
  exact hc


theorem mem_stdBorel_iff
    (hJ : (2 : Fin 4) ∈ J) (p : nativeParabolic J) :
    (p : ModGL Tag.E6 K) ∈ stdBorel ↔
      ((leviProj hJ p : stdLevi J) : ModGL Tag.E6 K) ∈ stdLeviBorel J := by
  refine ⟨leviProj_mem_stdLeviBorel hJ, fun h => ?_⟩
  have := mul_mem (stdRadical_le_stdBorel J (mul_inv_leviProj_mem hJ p))
    (stdLeviBorel_le_stdBorel J h)
  rwa [inv_mul_cancel_right] at this

abbrev ParabolicCosets
    (J : Set (Fin 4)) : Type :=
  nativeParabolic J ⧸ stdBorel.subgroupOf (nativeParabolic J)

abbrev LeviCosets
    (J : Set (Fin 4)) : Type :=
  stdLevi J ⧸ (stdLeviBorel J).subgroupOf (stdLevi J)

@[expose] def residueMap
    (hJ : (2 : Fin 4) ∈ J) : ParabolicCosets J → LeviCosets J :=
  Quotient.lift (fun p => (QuotientGroup.mk (leviProj hJ p) : LeviCosets J)) fun x y hxy => by
    have h : x⁻¹ * y ∈ stdBorel.subgroupOf (nativeParabolic J) :=
      QuotientGroup.leftRel_apply.mp hxy
    refine QuotientGroup.eq.mpr ?_
    rw [← map_inv, ← map_mul]
    exact leviProj_mem_stdLeviBorel hJ h

theorem residueMap_mk
    (hJ : (2 : Fin 4) ∈ J) (p : nativeParabolic J) :
    residueMap hJ (QuotientGroup.mk p) = QuotientGroup.mk (leviProj hJ p) :=
  rfl


theorem residueMap_bijective
    (hJ : (2 : Fin 4) ∈ J) : Function.Bijective (residueMap hJ) := by
  constructor
  · intro x y hxy
    induction x using QuotientGroup.induction_on with | H x => ?_
    induction y using QuotientGroup.induction_on with | H y => ?_
    rw [residueMap_mk, residueMap_mk, QuotientGroup.eq, ← map_inv, ← map_mul] at hxy
    exact QuotientGroup.eq.mpr ((mem_stdBorel_iff hJ (x⁻¹ * y)).mpr hxy)
  · intro y
    induction y using QuotientGroup.induction_on with | H l => ?_
    exact ⟨QuotientGroup.mk ⟨l, stdLevi_le_nativeParabolic hJ l.2⟩, by
      rw [residueMap_mk, leviProj_of_mem hJ l.2]⟩


@[expose] def leviParabolic
    (J I : Set (Fin 4)) : Subgroup (ModGL Tag.E6 K) :=
  Subgroup.closure ((stdLeviBorel J : Set (ModGL Tag.E6 K)) ∪ nativeRep '' I)

theorem leviParabolic_le_stdLevi
    (hJ : (2 : Fin 4) ∈ J) {I : Set (Fin 4)} (hIJ : I ⊆ J) :
    leviParabolic J I ≤ stdLevi J := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x (hx | ⟨i, hi, rfl⟩)
  · exact stdLeviBorel_le_stdLevi hJ hx
  · exact nativeRep_mem_stdLevi (hIJ hi)

theorem leviParabolic_le_nativeParabolic
    (J : Set (Fin 4)) (I : Set (Fin 4)) :
    leviParabolic J I ≤ nativeParabolic I := by
  refine (Subgroup.closure_le _).2 ?_
  rintro x (hx | ⟨i, hi, rfl⟩)
  · exact Subgroup.subset_closure (Or.inl (stdLeviBorel_le_stdBorel J hx))
  · exact Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩)

theorem mem_nativeParabolic_iff
    (hJ : (2 : Fin 4) ∈ J) {I : Set (Fin 4)} (hIJ : I ⊆ J)
    (p : nativeParabolic J) :
    (p : ModGL Tag.E6 K) ∈ nativeParabolic I ↔
      ((leviProj hJ p : stdLevi J) : ModGL Tag.E6 K) ∈ leviParabolic J I := by
  constructor
  · intro hp
    let S : Subgroup (nativeParabolic J) :=
      (leviParabolic J I).comap ((stdLevi J).subtype.comp (leviProj hJ))
    have hle : nativeParabolic I ≤ S.map (nativeParabolic J).subtype := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x (hx | ⟨i, hi, rfl⟩)
      · refine ⟨⟨x, stdBorel_le_nativeParabolic J hx⟩, ?_, rfl⟩
        exact Subgroup.subset_closure (Or.inl (leviProj_mem_stdLeviBorel hJ hx))
      · refine ⟨⟨nativeRep i, nativeRep_mem_nativeParabolic (hIJ hi)⟩, ?_, rfl⟩
        change ((leviProj hJ _ : stdLevi J) : ModGL Tag.E6 K) ∈ leviParabolic J I
        rw [leviProj_of_mem hJ (nativeRep_mem_stdLevi (hIJ hi))]
        exact Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩)
    obtain ⟨p', hp', hpp'⟩ := hle hp
    rw [show p = p' from Subtype.ext hpp'.symm]
    exact hp'
  · intro h
    have := mul_mem ((stdRadical_le_stdBorel J).trans (stdBorel_le_nativeParabolic I)
      (mul_inv_leviProj_mem hJ p)) (leviParabolic_le_nativeParabolic J I h)
    rwa [inv_mul_cancel_right] at this

theorem adjacent_iff
    (hJ : (2 : Fin 4) ∈ J) {I : Set (Fin 4)} (hIJ : I ⊆ J)
    (x y : nativeParabolic J) :
    ((x⁻¹ * y : nativeParabolic J) : ModGL Tag.E6 K) ∈ nativeParabolic I ↔
      (((leviProj hJ x)⁻¹ * leviProj hJ y : stdLevi J) : ModGL Tag.E6 K) ∈ leviParabolic J I := by
  rw [mem_nativeParabolic_iff hJ hIJ, map_mul, map_inv]


theorem leviProj_betaGL
    (hJ : (2 : Fin 4) ∈ J) (p : nativeParabolic J) :
    ((leviProj hJ ⟨betaGL p, betaGL_mem_nativeParabolic p.2⟩ : stdLevi J) : ModGL Tag.E6 K) =
      betaGL ((leviProj hJ p : stdLevi J) : ModGL Tag.E6 K) := by
  obtain ⟨⟨q, l⟩, ⟨hq, hl, hpql⟩, -⟩ := existsUnique_stdRadical_mul_stdLevi hJ p.2
  have hβp : betaGL (p : ModGL Tag.E6 K) = betaGL q * betaGL l := by
    rw [hpql, map_mul]
  have e : (⟨betaGL p, betaGL_mem_nativeParabolic p.2⟩ : nativeParabolic J) =
      ⟨betaGL q * betaGL l, hβp ▸ betaGL_mem_nativeParabolic p.2⟩ := Subtype.ext hβp
  have e' : p = ⟨q * l, hpql ▸ p.2⟩ := Subtype.ext hpql
  rw [e, leviProj_mul hJ (betaGL_mem_stdRadical hq) (betaGL_mem_stdLevi hl), e',
    leviProj_mul hJ hq hl]

theorem residueMap_betaGL
    (hJ : (2 : Fin 4) ∈ J) (p : nativeParabolic J) :
    residueMap hJ (QuotientGroup.mk ⟨betaGL p, betaGL_mem_nativeParabolic p.2⟩) =
      QuotientGroup.mk ⟨betaGL ((leviProj hJ p : stdLevi J) : ModGL Tag.E6 K),
        betaGL_mem_stdLevi (leviProj hJ p).2⟩ := by
  rw [residueMap_mk]
  congr 1
  exact Subtype.ext (leviProj_betaGL hJ p)


end CFSG.LieType.Chevalley.C2E6Std
