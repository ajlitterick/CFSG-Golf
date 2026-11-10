module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.LocalAnalysis.ComponentClassification.FixedCommutingProduct

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.ComponentClassification.CentralExtensions
open scoped commutatorElement

section General

variable {G : Type*} [Group G]

theorem mem_fixedSubgroup_iff {a : MulAut G} {x : G} : x ∈ fixedSubgroup a ↔ a x = x :=
  Iff.rfl

theorem apply_mem_center (a : MulAut G) {z : G} (hz : z ∈ center G) : a z ∈ center G :=
  mem_center_iff.mpr fun g => by
    obtain ⟨y, rfl⟩ := a.surjective g
    rw [← map_mul, ← map_mul, mem_center_iff.mp hz y]

@[expose] def centralDisplacement (a : MulAut G) {T : Subgroup G}
    (hT : ∀ x ∈ T, x⁻¹ * a x ∈ center G) : T →* G where
  toFun x := (x : G)⁻¹ * a x
  map_one' := by simp
  map_mul' x y := by
    have hc := mem_center_iff.mp (hT x x.2) (y : G)⁻¹
    change ((x : G) * y)⁻¹ * a ((x : G) * y) = ((x : G)⁻¹ * a x) * ((y : G)⁻¹ * a y)
    rw [map_mul, mul_inv_rev]
    calc (y : G)⁻¹ * (x : G)⁻¹ * (a x * a y) = (y : G)⁻¹ * ((x : G)⁻¹ * a x) * a y := by group
      _ = (x : G)⁻¹ * a x * (y : G)⁻¹ * a y := by rw [hc]
      _ = (x : G)⁻¹ * a x * ((y : G)⁻¹ * a y) := by group


@[expose] def centralNorm {K : Subgroup G} (hK : K ≤ center G) (a : MulAut G) : K →* G where
  toFun k := (k : G) * a k
  map_one' := by simp
  map_mul' x y := by
    have hy := mem_center_iff.mp (hK y.2) (a x)
    change (x : G) * y * a ((x : G) * y) = (x : G) * a x * ((y : G) * a y)
    rw [map_mul]
    calc (x : G) * y * (a x * a y) = (x : G) * (a x * y) * a y := by rw [hy]; group
      _ = (x : G) * a x * ((y : G) * a y) := by group


@[expose] def normKernel {K : Subgroup G} (hK : K ≤ center G) (a : MulAut G) : Subgroup G :=
  (centralNorm hK a).ker.map K.subtype

@[expose] def centralDifference {K : Subgroup G} (hK : K ≤ center G) (a : MulAut G) : K →* G :=
  centralDisplacement a fun _ hk => mul_mem (inv_mem (hK hk)) (apply_mem_center a (hK hk))

@[expose] def differenceImage {K : Subgroup G} (hK : K ≤ center G) (a : MulAut G) :
    Subgroup G :=
  (centralDifference hK a).range


variable {K : Subgroup G} {hK : K ≤ center G} {a : MulAut G}

theorem mem_normKernel {x : G} : x ∈ normKernel hK a ↔ x ∈ K ∧ x * a x = 1 := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem mem_differenceImage {x : G} : x ∈ differenceImage hK a ↔ ∃ k ∈ K, k⁻¹ * a k = x := by
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩


theorem normKernel_le : normKernel hK a ≤ K := fun _ hx => (mem_normKernel.mp hx).1

instance isMulCommutative_normKernel (hK : K ≤ center G) (a : MulAut G) :
    IsMulCommutative (normKernel hK a) :=
  isMulCommutative_iff.mpr fun x y =>
    Subtype.ext (mem_center_iff.mp (hK (normKernel_le y.2)) x)

theorem sq_mem_differenceImage {j : G} (hj : j ∈ normKernel hK a) :
    j ^ 2 ∈ differenceImage hK a := by
  obtain ⟨hjK, hj1⟩ := mem_normKernel.mp hj
  have haj : a j = j⁻¹ := eq_inv_of_mul_eq_one_right hj1
  refine mem_differenceImage.mpr ⟨j⁻¹, inv_mem hjK, ?_⟩
  rw [inv_inv, map_inv, haj, inv_inv, sq]

theorem isElementaryAbelian_normKernel_quotient :
    IsElementaryAbelian 2
      (normKernel hK a ⧸ (differenceImage hK a).subgroupOf (normKernel hK a)) := by
  have hcomm : IsMulCommutative
      (normKernel hK a ⧸ (differenceImage hK a).subgroupOf (normKernel hK a)) := by
    refine isMulCommutative_iff.mpr fun x y => ?_
    induction x using QuotientGroup.induction_on with | H x => ?_
    induction y using QuotientGroup.induction_on with | H y => ?_
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      isMulCommutative_iff.mp inferInstance x y]
  refine
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_ }
  induction x using QuotientGroup.induction_on with | H j => ?_
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact sq_mem_differenceImage j.2


theorem isElementaryAbelian_of_injective {p : ℕ} {H : Type*} [Group H]
    [hH : IsElementaryAbelian p H] {f : G →* H} (hf : Function.Injective f) :
    IsElementaryAbelian p G := by
  have hcomm : IsMulCommutative G := isMulCommutative_iff.mpr fun x y =>
    hf (by rw [map_mul, map_mul, isMulCommutative_iff.mp inferInstance (f x) (f y)])
  refine
    { toIsMulCommutative := hcomm
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => hf ?_ }
  rw [map_pow, map_one]
  exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hH.exponent_dvd_p (f x)


end General

section CentralKernel

variable {L S : Type*} [Group L] [Group S] {π : L →* S} {a : MulAut L} {α : MulAut S}


theorem inv_mul_apply_mem_ker (hcomm : ∀ x, π (a x) = α (π x)) {x : L} (hx : α (π x) = π x) :
    x⁻¹ * a x ∈ π.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_inv, hcomm, hx, inv_mul_cancel]

theorem fixedPerfectLift (hπ : Function.Surjective π) (hK : π.ker ≤ center L)
    (hcomm : ∀ x, π (a x) = α (π x)) (P : Subgroup S) [Group.IsPerfect P]
    (hP : ∀ s ∈ P, α s = s) :
    Group.IsPerfect ↥⁅P.comap π, P.comap π⁆ ∧ ⁅P.comap π, P.comap π⁆.map π = P ∧
      ∀ x ∈ ⁅P.comap π, P.comap π⁆, a x = x := by
  set D := P.comap π with hD
  have hdisp : ∀ x ∈ D, x⁻¹ * a x ∈ center L := fun x hx =>
    hK (inv_mul_apply_mem_ker hcomm (hP _ hx))
  have hfix : ⁅D, D⁆ ≤ fixedSubgroup a := by
    rw [commutator_le]
    intro x hx y hy
    change a ⁅x, y⁆ = ⁅x, y⁆
    calc a ⁅x, y⁆ = ⁅a x, a y⁆ := map_commutatorElement a x y
      _ = ⁅x * (x⁻¹ * a x), y * (y⁻¹ * a y)⁆ := by rw [mul_inv_cancel_left, mul_inv_cancel_left]
      _ = ⁅x, y⁆ := by
        rw [commutator_mul_center_left _ _ _ (hdisp x hx),
          commutator_mul_center_right _ _ _ (hdisp y hy)]
  have hmap : ⁅D, D⁆.map π = P := by
    rw [map_commutator, map_comap_eq_self_of_surjective hπ, commutator_eq_self]
  have hsup : ⁅D, D⁆ ⊔ π.ker = D := by
    rw [← comap_map_eq, hmap]
  have hperf : ⁅⁅D, D⁆, ⁅D, D⁆⁆ = ⁅D, D⁆ := by
    conv_rhs => rw [← hsup]
    exact (commutator_sup_central _ _ hK).symm
  exact ⟨isPerfect_iff.mpr hperf, hmap, fun x hx => hfix hx⟩


variable (hK : π.ker ≤ center L)

theorem inv_mul_apply_mem_normKernel (ha : ∀ x, a (a x) = x) (hcomm : ∀ x, π (a x) = α (π x))
    {x : L} (hx : π x ∈ fixedSubgroup α) : x⁻¹ * a x ∈ normKernel hK a := by
  refine mem_normKernel.mpr ⟨inv_mul_apply_mem_ker hcomm hx, ?_⟩
  rw [map_mul, map_inv, ha]
  group


theorem exists_fixedImageHom (hπ : Function.Surjective π) (ha : ∀ x, a (a x) = x)
    (hcomm : ∀ x, π (a x) = α (π x)) :
    ∃ θ : fixedSubgroup α →*
        normKernel hK a ⧸ (differenceImage hK a).subgroupOf (normKernel hK a),
      (∀ (x : L) (hx : π x ∈ fixedSubgroup α) (hxJ : x⁻¹ * a x ∈ normKernel hK a),
        θ ⟨π x, hx⟩ = ((⟨x⁻¹ * a x, hxJ⟩ : normKernel hK a) :
          normKernel hK a ⧸ (differenceImage hK a).subgroupOf (normKernel hK a))) ∧
      θ.ker = ((fixedSubgroup a).map π).subgroupOf (fixedSubgroup α) := by
  set T := (fixedSubgroup α).comap π
  have hT : ∀ x ∈ T, x⁻¹ * a x ∈ center L := fun x hx => hK (inv_mul_apply_mem_ker hcomm hx)
  let δ : T →* normKernel hK a := (centralDisplacement a hT).codRestrict _
    fun x => inv_mul_apply_mem_normKernel hK ha hcomm x.2
  let q := QuotientGroup.mk' ((differenceImage hK a).subgroupOf (normKernel hK a))
  let πT := π.subgroupComap (fixedSubgroup α)
  have hsurj : Function.Surjective πT := π.subgroupComap_surjective _ hπ
  have hker : πT.ker ≤ (q.comp δ).ker := by
    intro x hx
    have hxK : (x : L) ∈ π.ker := congrArg Subtype.val hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact mem_differenceImage.mpr ⟨x, hxK, rfl⟩
  let θ := πT.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj)
    ⟨q.comp δ, hker⟩
  have hθ : ∀ x : T, θ (πT x) = q (δ x) := fun x =>
    πT.liftOfRightInverse_comp_apply _ _ ⟨q.comp δ, hker⟩ x
  refine ⟨θ, fun x hx _ => hθ ⟨x, hx⟩, ?_⟩
  ext c
  rw [MonoidHom.mem_ker, mem_subgroupOf]
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := hsurj c
    rw [hθ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf] at h
    obtain ⟨k, hk, hkx⟩ := mem_differenceImage.mp h
    have hkx' : k⁻¹ * a k = (x : L)⁻¹ * a x := hkx
    refine ⟨x * k⁻¹, ?_, ?_⟩
    · have hax : a x = x * (k⁻¹ * a k) := by rw [hkx']; group
      change a ((x : L) * k⁻¹) = x * k⁻¹
      rw [map_mul, map_inv, hax]
      group
    · rw [map_mul, map_inv, MonoidHom.mem_ker.mp hk, inv_one, mul_one]
      rfl
  · rintro ⟨y, hy, hyc⟩
    have hyT : y ∈ T := by
      change α (π y) = π y
      rw [← hcomm, mem_fixedSubgroup_iff.mp hy]
    have hc : c = πT ⟨y, hyT⟩ := Subtype.ext hyc.symm
    rw [hc, hθ]
    have hδ : δ ⟨y, hyT⟩ = 1 := Subtype.ext (by
      change y⁻¹ * a y = 1
      rw [mem_fixedSubgroup_iff.mp hy, inv_mul_cancel])
    rw [hδ, map_one]

theorem fixedImage_normal (hK : π.ker ≤ center L) (hπ : Function.Surjective π)
    (ha : ∀ x, a (a x) = x)
    (hcomm : ∀ x, π (a x) = α (π x)) :
    (((fixedSubgroup a).map π).subgroupOf (fixedSubgroup α)).Normal := by
  obtain ⟨θ, -, hθ⟩ := exists_fixedImageHom hK hπ ha hcomm
  rw [← hθ]
  infer_instance

theorem fixedImage_quotient_embedding (hπ : Function.Surjective π) (ha : ∀ x, a (a x) = x)
    (hcomm : ∀ x, π (a x) = α (π x)) :
    ∃ _ : (((fixedSubgroup a).map π).subgroupOf (fixedSubgroup α)).Normal,
      (∃ φ : fixedSubgroup α ⧸ ((fixedSubgroup a).map π).subgroupOf (fixedSubgroup α) →*
          normKernel hK a ⧸ (differenceImage hK a).subgroupOf (normKernel hK a),
        Function.Injective φ) ∧
      IsElementaryAbelian 2
        (fixedSubgroup α ⧸ ((fixedSubgroup a).map π).subgroupOf (fixedSubgroup α)) := by
  obtain ⟨θ, -, hθ⟩ := exists_fixedImageHom hK hπ ha hcomm
  have hN := fixedImage_normal hK hπ ha hcomm
  refine ⟨hN, ?_⟩
  let φ := (QuotientGroup.kerLift θ).comp (QuotientGroup.quotientMulEquivOfEq hθ.symm).toMonoidHom
  have hφ : Function.Injective φ :=
    (QuotientGroup.kerLift_injective θ).comp (MulEquiv.injective _)
  have := isElementaryAbelian_normKernel_quotient (hK := hK) (a := a)
  exact ⟨⟨φ, hφ⟩, isElementaryAbelian_of_injective hφ⟩


end CentralKernel

end CFSG.LocalAnalysis.ComponentInitial
