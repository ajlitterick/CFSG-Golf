module

public import CFSG.CharacterTheory.Wreathed.CentralizerResidual
public import CFSG.CharacterTheory.Wreathed.FullCenterOddCore
public import CFSG.LocalAnalysis.ComponentClassification.OddCore
public import CFSG.CharacterTheory.Wreathed.QuaternionCentralQuotient

public noncomputable section

namespace CFSG.Wreathed

open scoped Classical

universe u v

variable {G : Type u} [Group G]

theorem centralizerOddCore_le_transferKernel [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerOddCore n S e ≤ centralizerTransferKernel n hn S e := by
  intro g hg
  apply centralizerTransferKernel_odd_order_mem n hn S e
  exact (weakClosure_oddCore_card (involutionCentralizer n S e)).of_dvd_nat
    ((centralizerOddCore n S e).orderOf_dvd_natCard hg)


@[expose] def centralizerResidualImage [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup (centralizerOddCoreQuotient n S e) :=
  (centralizerTransferKernel n hn S e).map (centralizerOddCoreMap n S e)

instance centralizerResidualImage_normal [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerResidualImage n hn S e).Normal :=
  Subgroup.Normal.map inferInstance _ (centralizerOddCoreMap_surjective n S e)

@[expose] def centralizerResidualMap [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerTransferKernel n hn S e →* centralizerResidualImage n hn S e :=
  (centralizerOddCoreMap n S e).subgroupMap (centralizerTransferKernel n hn S e)


theorem centralizerResidualMap_surjective [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Function.Surjective (centralizerResidualMap n hn S e) :=
  (centralizerOddCoreMap n S e).subgroupMap_surjective _


theorem centralizerResidualImage_index [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerResidualImage n hn S e).index = 2 ^ n := by
  have hk : (centralizerOddCoreMap n S e).ker = centralizerOddCore n S e :=
    QuotientGroup.ker_mk' _
  change ((centralizerTransferKernel n hn S e).map (centralizerOddCoreMap n S e)).index = _
  rw [Subgroup.index_map_eq (centralizerTransferKernel n hn S e)
    (centralizerOddCoreMap_surjective n S e) (by
      rw [hk]
      exact centralizerOddCore_le_transferKernel n hn S e)]
  exact centralizerTransferKernel_index hnonab n hn S e


@[expose] def centralizerKernelSylow [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Sylow 2 (centralizerTransferKernel n hn S e) :=
  (centralizerTransferKernel_sylow hnonab n hn S e).choose

theorem centralizerKernelSylow_eq [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerKernelSylow hnonab n hn S e : Subgroup (centralizerTransferKernel n hn S e)) =
      (centralizerQuaternion n hn S e).subgroupOf (centralizerTransferKernel n hn S e) :=
  (centralizerTransferKernel_sylow hnonab n hn S e).choose_spec

theorem centralizerKernelSylow_mem_quaternion [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (s : centralizerKernelSylow hnonab n hn S e) :
    ((s : centralizerTransferKernel n hn S e) : involutionCentralizer n S e) ∈
      centralizerQuaternion n hn S e := by
  have h := s.property
  change (s : centralizerTransferKernel n hn S e) ∈
    (centralizerKernelSylow hnonab n hn S e : Subgroup (centralizerTransferKernel n hn S e)) at h
  rw [centralizerKernelSylow_eq] at h
  exact h

@[expose] def centralizerResidualSylow [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Sylow 2 (centralizerResidualImage n hn S e) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (centralizerKernelSylow hnonab n hn S e).mapSurjective
    (centralizerResidualMap_surjective n hn S e)

theorem centralizerResidualMap_comp [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerResidualImage n hn S e).subtype.comp (centralizerResidualMap n hn S e) =
      (centralizerOddCoreMap n S e).comp (centralizerTransferKernel n hn S e).subtype := rfl

theorem centralizerResidualSylow_image [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerResidualSylow hnonab n hn S e : Subgroup (centralizerResidualImage n hn S e)).map
      (centralizerResidualImage n hn S e).subtype =
        (centralizerQuaternion n hn S e).map (centralizerOddCoreMap n S e) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [centralizerResidualSylow, Sylow.coe_mapSurjective, Subgroup.map_map,
    centralizerResidualMap_comp, ← Subgroup.map_map, centralizerKernelSylow_eq,
    Subgroup.map_subgroupOf_eq_of_le (centralizerQuaternion_le_transferKernel hnonab n hn S e)]

theorem centralizerResidualMap_sylow_injective [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Function.Injective ((centralizerResidualMap n hn S e).domRestrict
      (centralizerKernelSylow hnonab n hn S e : Subgroup (centralizerTransferKernel n hn S e))) := by
  intro a b hab
  let aN : centralizerSylow n hn S e :=
    ⟨((a : centralizerTransferKernel n hn S e) : involutionCentralizer n S e),
      centralizerQuaternion_le_sylow n hn S e
        (centralizerKernelSylow_mem_quaternion hnonab n hn S e a)⟩
  let bN : centralizerSylow n hn S e :=
    ⟨((b : centralizerTransferKernel n hn S e) : involutionCentralizer n S e),
      centralizerQuaternion_le_sylow n hn S e
        (centralizerKernelSylow_mem_quaternion hnonab n hn S e b)⟩
  have hN : aN = bN := centralizerOddCoreMap_sylow_injective n hn S e
    (congrArg Subtype.val hab)
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun x : centralizerSylow n hn S e => (x : involutionCentralizer n S e)) hN

@[expose] def centralizerResidualSylowEquiv [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerKernelSylow hnonab n hn S e ≃* centralizerResidualSylow hnonab n hn S e := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine MulEquiv.ofBijective ((centralizerResidualMap n hn S e).subgroupMap
    (centralizerKernelSylow hnonab n hn S e : Subgroup (centralizerTransferKernel n hn S e))) ⟨?_, ?_⟩
  · intro a b hab
    exact centralizerResidualMap_sylow_injective hnonab n hn S e (congrArg Subtype.val hab)
  · exact (centralizerResidualMap n hn S e).subgroupMap_surjective _

theorem centralizerResidualSylowEquiv_coe [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (s : centralizerKernelSylow hnonab n hn S e) :
    (centralizerResidualSylowEquiv hnonab n hn S e s : centralizerResidualImage n hn S e) =
      centralizerResidualMap n hn S e (s : centralizerTransferKernel n hn S e) := rfl

@[expose] def centralizerKernelQuaternionCoordinates [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    QuaternionGroup (2 ^ n / 2) ≃* centralizerKernelSylow hnonab n hn S e :=
  ((originalYQuaternionEquiv n hn).trans
    (modelYEquiv (centralizerSylow n hn S e) (centralizerCoordinates n hn S e))).trans
      ((Subgroup.subgroupOfEquivOfLe (centralizerQuaternion_le_transferKernel hnonab n hn S e)).symm.trans
        (MulEquiv.subgroupCongr (centralizerKernelSylow_eq hnonab n hn S e).symm))


@[expose] def centralizerResidualQuaternionEquiv [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    QuaternionGroup (2 ^ n / 2) ≃* centralizerResidualSylow hnonab n hn S e :=
  (centralizerKernelQuaternionCoordinates hnonab n hn S e).trans
    (centralizerResidualSylowEquiv hnonab n hn S e)


theorem centralizerResidualSylow_card [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card (centralizerResidualSylow hnonab n hn S e) = 2 * 2 ^ n := by
  rw [← Nat.card_congr (centralizerResidualSylowEquiv hnonab n hn S e).toEquiv]
  rw [centralizerKernelSylow_eq,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (centralizerQuaternion_le_transferKernel hnonab n hn S e)).toEquiv]
  exact centralizerQuaternion_card n hn S e

theorem centralizerKernelInvolution_original_order (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    orderOf (centralInvolution n S e) = 2 := by
  change orderOf (wreathModelHom (centralizerSylow n hn S e) (centralizerCoordinates n hn S e)
    (Original.x (2 ^ n))) = 2
  rw [orderOf_injective _ (wreathModelHom_injective _ _)]
  exact (wreath_center_involution_and_quaternion_coordinates n hn).involution_orders.1

theorem centralizerKernelInvolution_original_mem_quaternion (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralInvolution n S e ∈ centralizerQuaternion n hn S e :=
  Subgroup.mem_map_of_mem _ (original_x_mem_Y n hn)

@[expose] def centralizerKernelInvolution [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerTransferKernel n hn S e :=
  ⟨centralInvolution n S e, centralizerQuaternion_le_transferKernel hnonab n hn S e
    (centralizerKernelInvolution_original_mem_quaternion n hn S e)⟩

@[expose] def centralizerResidualInvolution [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerResidualImage n hn S e :=
  centralizerResidualMap n hn S e (centralizerKernelInvolution hnonab n hn S e)

theorem centralizerResidualInvolution_coe [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerResidualInvolution hnonab n hn S e : centralizerOddCoreQuotient n S e) =
      centralizerOddCoreMap n S e (centralInvolution n S e) := rfl

theorem centralizerResidualInvolution_mem_ambient_center [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerResidualInvolution hnonab n hn S e : centralizerOddCoreQuotient n S e) ∈
      Subgroup.center (centralizerOddCoreQuotient n S e) := by
  rw [centralizerResidualInvolution_coe]
  exact Subgroup.map_center_le_center (centralizerOddCoreMap_surjective n S e)
    (Subgroup.mem_map_of_mem _ (centralInvolution_mem_center n S e))

theorem centralizerResidualInvolution_mem_center [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerResidualInvolution hnonab n hn S e ∈ Subgroup.center (centralizerResidualImage n hn S e) := by
  apply Subgroup.mem_center_iff.mpr
  intro g
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp
    (centralizerResidualInvolution_mem_ambient_center hnonab n hn S e) g

theorem centralizerResidualInvolution_order [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    orderOf (centralizerResidualInvolution hnonab n hn S e) = 2 := by
  rw [← Subgroup.orderOf_coe, centralizerResidualInvolution_coe]
  let x : centralizerSylow n hn S e :=
    ⟨centralInvolution n S e,
      centralizerQuaternion_le_sylow n hn S e (centralizerKernelInvolution_original_mem_quaternion n hn S e)⟩
  have h := orderOf_injective ((centralizerOddCoreMap n S e).domRestrict
    (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)))
      (centralizerOddCoreMap_sylow_injective n hn S e) x
  change orderOf (centralizerOddCoreMap n S e (centralInvolution n S e)) = _ at h
  rw [h, ← Subgroup.orderOf_coe x]
  exact centralizerKernelInvolution_original_order n hn S e

theorem centralizerResidualSylow_unique_involution [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : centralizerResidualSylow hnonab n hn S e) (hy : orderOf y = 2) :
    (y : centralizerResidualImage n hn S e) = centralizerResidualInvolution hnonab n hn S e := by
  let E := centralizerResidualSylowEquiv hnonab n hn S e
  obtain ⟨s, rfl⟩ := E.surjective y
  have hs : orderOf s = 2 := (E.orderOf_eq s).symm.trans hy
  have hq : ((s : centralizerTransferKernel n hn S e) : involutionCentralizer n S e) =
      centralInvolution n S e :=
    centralizerQuaternion_unique_involution n hn S e _
      (centralizerKernelSylow_mem_quaternion hnonab n hn S e s)
      ((Subgroup.orderOf_coe _).trans ((Subgroup.orderOf_coe s).trans hs))
  rw [centralizerResidualSylowEquiv_coe]
  exact congrArg (centralizerResidualMap n hn S e)
    (Subtype.ext hq : (s : centralizerTransferKernel n hn S e) = centralizerKernelInvolution hnonab n hn S e)

theorem centralizerResidualImage_unique_involution [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : centralizerResidualImage n hn S e) (hy : orderOf y = 2) :
    y = centralizerResidualInvolution hnonab n hn S e := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htwo : IsPGroup 2 (Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy]; norm_num)
  obtain ⟨s, hys⟩ := CFSG.Semidihedral.InvolutionFusion.exists_ambient_conjugate_mem_sylow
    (centralizerResidualSylow hnonab n hn S e) y htwo
  have hs : orderOf s = 2 := by
    have horder : orderOf y = orderOf (s : centralizerResidualImage n hn S e) :=
      CFSG.Semidihedral.conjugate_orderOf_eq hys
    exact (Subgroup.orderOf_coe s).symm.trans (horder.symm.trans hy)
  rw [centralizerResidualSylow_unique_involution hnonab n hn S e s hs] at hys
  exact hys.eq_of_right_mem_center (centralizerResidualInvolution_mem_center hnonab n hn S e)


theorem centralizerQuaternionImage_card [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Nat.card ((centralizerQuaternion n hn S e).map (centralizerOddCoreMap n S e)) = 2 * 2 ^ n := by
  rw [← centralizerResidualSylow_image hnonab n hn S e, Subgroup.card_subtype]
  exact centralizerResidualSylow_card hnonab n hn S e

theorem centralizerResidualImage_unique_involution_ambient [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (y : centralizerOddCoreQuotient n S e) (hy : y ∈ centralizerResidualImage n hn S e)
    (horder : orderOf y = 2) : y = centralizerOddCoreMap n S e (centralInvolution n S e) := by
  have h := centralizerResidualImage_unique_involution hnonab n hn S e ⟨y, hy⟩
    ((Subgroup.orderOf_coe (⟨y, hy⟩ : centralizerResidualImage n hn S e)).symm.trans horder)
  exact congrArg Subtype.val h


@[expose] def centralizerQuaternionImageEquiv [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    QuaternionGroup (2 ^ n / 2) ≃*
      (centralizerQuaternion n hn S e).map (centralizerOddCoreMap n S e) :=
  (centralizerResidualQuaternionEquiv hnonab n hn S e).trans
    (((centralizerResidualSylow hnonab n hn S e :
      Subgroup (centralizerResidualImage n hn S e)).equivMapOfInjective
        (centralizerResidualImage n hn S e).subtype Subtype.coe_injective).trans
      (MulEquiv.subgroupCongr (centralizerResidualSylow_image hnonab n hn S e)))


theorem centralizerQuaternionImage_eq_modelY [Finite G]
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerQuaternion n hn S e).map (centralizerOddCoreMap n S e) =
      modelY (centralizerOddCoreSylow n hn S e) (centralizerOddCoreCoordinates n hn S e) := by
  rw [centralizerQuaternion, modelY, Subgroup.map_map, ← centralizerOddCoreModelHom_comp]
  rfl


end CFSG.Wreathed
