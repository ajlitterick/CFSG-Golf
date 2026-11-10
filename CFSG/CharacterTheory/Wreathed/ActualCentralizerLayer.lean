module

public import CFSG.CharacterTheory.Wreathed.DihedralLayerAlternatives
public import CFSG.CharacterTheory.Wreathed.UniqueInvolutionLift
public import CFSG.CharacterTheory.Wreathed.ArbitraryCentralizerKernel

public noncomputable section

namespace CFSG.Wreathed

universe u v

theorem wreathed_two_pow_div_two (n : ℕ) (hn : 1 ≤ n) :
    2 ^ n / 2 = 2 ^ (n - 1) := by
  conv_lhs => rw [show n = (n - 1) + 1 by omega]
  rw [pow_succ, Nat.mul_div_cancel _ (by decide : 0 < 2)]

variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

@[expose] def centralizerDihedralSylowExactEquiv
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerDihedralSylow hnonab n hn S e ≃* DihedralGroup (2 ^ (n - 1)) := by
  rw [← wreathed_two_pow_div_two n (by omega)]
  exact centralizerDihedralSylowEquiv hnonab n hn S e

theorem centralizerFullQuotient_layer_exactly_one
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (DihedralFourPointAlternative (centralizerFullQuotient n hn S e) n
        (centralizerDihedralImage n hn S e) ∨
      DihedralSimpleLayerAlternative (centralizerFullQuotient n hn S e) n
        (centralizerDihedralImage n hn S e)) ∧
    ¬ (DihedralFourPointAlternative (centralizerFullQuotient n hn S e) n
        (centralizerDihedralImage n hn S e) ∧
      DihedralSimpleLayerAlternative (centralizerFullQuotient n hn S e) n
        (centralizerDihedralImage n hn S e)) := by
  apply dihedral_layer_exactly_one n hn
    (centralizerFullQuotient_oddCore_eq_bot n hn S e)
    (centralizerFullQuotientSylow n hn S e) (centralizerFullQuotientSylowEquiv n hn S e)
    (centralizerDihedralImage n hn S e) (centralizerDihedralImage_index hnonab n hn S e)
    (centralizerDihedralSylow hnonab n hn S e)
    (centralizerDihedralSylowExactEquiv hnonab n hn S e)
  intro D _ _ hD f
  exact centralizerDihedralImage_hom_to_two_group_eq_one hnonab n hn S e hD f


theorem centralizerFullQuotient_simple_layer_of_not_symmetric_four
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    DihedralSimpleLayerAlternative (centralizerFullQuotient n hn S e) n
      (centralizerDihedralImage n hn S e) := by
  rcases (centralizerFullQuotient_layer_exactly_one hnonab n hn S e).1 with h | h
  · rw [DihedralFourPointAlternative] at h
    obtain ⟨_, φ, _⟩ := h
    exact (hfour ⟨φ⟩).elim
  · exact h

@[expose] def centralizerSimpleLayer (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup (centralizerFullQuotient n hn S e) :=
  CFSG.generalizedFitting (centralizerFullQuotient n hn S e)

instance centralizerSimpleLayer_normal (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerSimpleLayer n hn S e).Normal := by
  change (CFSG.generalizedFitting (centralizerFullQuotient n hn S e)).Normal
  infer_instance

@[expose] def centralizerLiftedLayer (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    Subgroup (centralizerOddCoreQuotient n S e) :=
  UniqueInvolutionLift.liftedSubgroup (centralizerFullQuotientMap n hn S e)
    (centralizerResidualImage n hn S e) (centralizerSimpleLayer n hn S e)

instance centralizerLiftedLayer_normal (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerLiftedLayer n hn S e).Normal := by
  change (UniqueInvolutionLift.liftedSubgroup (centralizerFullQuotientMap n hn S e)
    (centralizerResidualImage n hn S e) (centralizerSimpleLayer n hn S e)).Normal
  infer_instance

@[expose] def centralizerLiftedLayerMap (n : ℕ) (hn : 2 ≤ n)
    (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    centralizerLiftedLayer n hn S e →* centralizerSimpleLayer n hn S e :=
  UniqueInvolutionLift.restrictedMap (centralizerFullQuotientMap n hn S e)
    (centralizerResidualImage n hn S e) (centralizerSimpleLayer n hn S e)

theorem even_card_of_dihedral_sylow {E : Type u} [Group E] [Finite E]
    (U : Sylow 2 E) (m : ℕ) (eU : U ≃* DihedralGroup m) : Even (Nat.card E) := by
  have hcard : Nat.card U = 2 * m :=
    (Nat.card_congr eU.toEquiv).trans DihedralGroup.nat_card
  have hdvd : 2 ∣ Nat.card U := hcard.symm ▸ dvd_mul_right 2 m
  exact even_iff_two_dvd.mpr (hdvd.trans (Subgroup.card_subgroup_dvd_card (U : Subgroup E)))

theorem centralizerSimpleLayer_even
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    Even (Nat.card (centralizerSimpleLayer n hn S e)) := by
  have h := centralizerFullQuotient_simple_layer_of_not_symmetric_four hnonab n hn S e hfour
  rw [DihedralSimpleLayerAlternative] at h
  change Even (Nat.card (CFSG.generalizedFitting (centralizerFullQuotient n hn S e)))
  let U : Sylow 2 (CFSG.generalizedFitting (centralizerFullQuotient n hn S e)) :=
    Classical.choice Sylow.nonempty
  obtain ⟨eU⟩ := h.2.2.2.2.2.1 U
  exact even_card_of_dihedral_sylow U (2 ^ (n - 1)) eU

theorem wreathed_centralizer_unique_component_data
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    UniqueInvolutionLift.UniqueInvolutionLiftData (centralizerFullQuotientMap n hn S e)
      (centralizerResidualImage n hn S e) (centralizerSimpleLayer n hn S e)
      (centralizerOddCoreMap n S e (centralInvolution n S e)) := by
  have h := centralizerFullQuotient_simple_layer_of_not_symmetric_four hnonab n hn S e hfour
  rw [DihedralSimpleLayerAlternative] at h
  let : IsSimpleGroup (centralizerSimpleLayer n hn S e) := h.1
  apply UniqueInvolutionLift.unique_involution_residual_lifts_simple_layer
    (centralizerFullQuotientMap n hn S e) (centralizerFullQuotientMap_surjective n hn S e)
    (centralizerResidualImage n hn S e) (centralizerSimpleLayer n hn S e)
    h.2.2.2.1 h.2.1 (centralizerSimpleLayer_even hnonab n hn S e hfour)
  · change (QuotientGroup.mk' (centralizerFullCenterImage n hn S e)).ker ≤ _
    rw [QuotientGroup.ker_mk']
    exact (centralizerFullCenterImage_le_center_and_factorization n hn S e).1
  · exact h.2.2.1
  · exact (Subgroup.orderOf_coe (centralizerResidualInvolution hnonab n hn S e)).trans
      (centralizerResidualInvolution_order hnonab n hn S e)
  · change (QuotientGroup.mk' (centralizerFullCenterImage n hn S e)).ker ⊓ _ = _
    rw [QuotientGroup.ker_mk']
    exact centralizerFullCenterImage_inf_residualImage hnonab n hn S e
  · intro t ht horder
    exact centralizerResidualImage_unique_involution_ambient hnonab n hn S e t ht horder

omit [IsSimpleGroup G] in
theorem centralizerLiftedLayer_relIndex_eq
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n)) :
    (centralizerLiftedLayer n hn S e).relIndex (centralizerResidualImage n hn S e) =
      (centralizerSimpleLayer n hn S e).relIndex (centralizerDihedralImage n hn S e) := by
  rw [centralizerLiftedLayer, UniqueInvolutionLift.liftedSubgroup,
    Subgroup.inf_relIndex_left, Subgroup.relIndex_comap]
  rfl

theorem centralizerLiftedLayer_odd_relIndex
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    Odd ((centralizerLiftedLayer n hn S e).relIndex (centralizerResidualImage n hn S e)) := by
  rw [centralizerLiftedLayer_relIndex_eq]
  have h := centralizerFullQuotient_simple_layer_of_not_symmetric_four hnonab n hn S e hfour
  rw [DihedralSimpleLayerAlternative] at h
  exact h.2.2.2.2.1

theorem two_subgroup_le_normal_of_odd_index
    {E : Type u} [Group E] [Finite E] (P M : Subgroup E) [M.Normal]
    (hP : IsPGroup 2 P) (hM : Odd M.index) : P ≤ M := by
  apply Subgroup.relIndex_eq_one.mp
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  exact Nat.eq_one_of_dvd_coprimes
    (Nat.prime_two.coprime_pow_of_not_dvd hM.not_two_dvd_nat)
    (M.relIndex_dvd_index_of_normal P)
    ((Subgroup.relIndex_dvd_card M P).trans (dvd_of_eq hk))

theorem centralizerResidualSylow_le_liftedLayer
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    ((centralizerResidualSylow hnonab n hn S e : Subgroup (centralizerResidualImage n hn S e)).map
      (centralizerResidualImage n hn S e).subtype) ≤ centralizerLiftedLayer n hn S e := by
  let M := (centralizerLiftedLayer n hn S e).subgroupOf (centralizerResidualImage n hn S e)
  have : M.Normal := by dsimp only [M]; infer_instance
  have hodd : Odd M.index := centralizerLiftedLayer_odd_relIndex hnonab n hn S e hfour
  have hle := two_subgroup_le_normal_of_odd_index
    (centralizerResidualSylow hnonab n hn S e : Subgroup (centralizerResidualImage n hn S e)) M
    (centralizerResidualSylow hnonab n hn S e).isPGroup' hodd
  rintro x ⟨y, hy, rfl⟩
  exact hle hy

@[expose] def centralizerLiftedLayerSylow
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    Sylow 2 (centralizerLiftedLayer n hn S e) := by
  let M := (centralizerLiftedLayer n hn S e).subgroupOf (centralizerResidualImage n hn S e)
  have hle : (centralizerResidualSylow hnonab n hn S e : Subgroup (centralizerResidualImage n hn S e)) ≤ M :=
    Subgroup.map_le_iff_le_comap.mp (centralizerResidualSylow_le_liftedLayer hnonab n hn S e hfour)
  let Q : Sylow 2 M := (centralizerResidualSylow hnonab n hn S e).subtype hle
  let eM : M ≃* centralizerLiftedLayer n hn S e :=
    Subgroup.subgroupOfEquivOfLe (by
      change UniqueInvolutionLift.liftedSubgroup _ _ _ ≤ _
      exact inf_le_left)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heM : Function.Surjective eM.toMonoidHom := by
    intro m
    exact ⟨eM.symm m, eM.apply_symm_apply m⟩
  exact Q.mapSurjective heM


theorem centralizerLiftedLayerSylow_image
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    (centralizerLiftedLayerSylow hnonab n hn S e hfour : Subgroup (centralizerLiftedLayer n hn S e)).map
      (centralizerLiftedLayer n hn S e).subtype =
      (centralizerQuaternion n hn S e).map (centralizerOddCoreMap n S e) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let M := (centralizerLiftedLayer n hn S e).subgroupOf (centralizerResidualImage n hn S e)
  have hle : (centralizerResidualSylow hnonab n hn S e : Subgroup (centralizerResidualImage n hn S e)) ≤ M :=
    Subgroup.map_le_iff_le_comap.mp (centralizerResidualSylow_le_liftedLayer hnonab n hn S e hfour)
  let eM : M ≃* centralizerLiftedLayer n hn S e :=
    Subgroup.subgroupOfEquivOfLe (by
      change UniqueInvolutionLift.liftedSubgroup _ _ _ ≤ _
      exact inf_le_left)
  have hcomp : (centralizerLiftedLayer n hn S e).subtype.comp eM.toMonoidHom =
      (centralizerResidualImage n hn S e).subtype.comp M.subtype := rfl
  have hmap : (centralizerLiftedLayerSylow hnonab n hn S e hfour : Subgroup (centralizerLiftedLayer n hn S e)) =
      ((centralizerResidualSylow hnonab n hn S e).subtype hle : Subgroup M).map eM.toMonoidHom := by
    rfl
  rw [hmap, Subgroup.map_map]
  change ((centralizerResidualSylow hnonab n hn S e).subtype hle : Subgroup M).map
    ((centralizerLiftedLayer n hn S e).subtype.comp eM.toMonoidHom) = _
  rw [hcomp, ← Subgroup.map_map, Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hle]
  exact centralizerResidualSylow_image hnonab n hn S e

@[expose] def centralizerLiftedLayerQuaternionEquiv
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    QuaternionGroup (2 ^ n / 2) ≃* centralizerLiftedLayerSylow hnonab n hn S e hfour := by
  let Q := (centralizerQuaternion n hn S e).map (centralizerOddCoreMap n S e)
  let U := centralizerLiftedLayerSylow hnonab n hn S e hfour
  let eU : U ≃* Q := ((U : Subgroup (centralizerLiftedLayer n hn S e)).equivMapOfInjective
      (centralizerLiftedLayer n hn S e).subtype Subtype.coe_injective).trans
    (MulEquiv.subgroupCongr (centralizerLiftedLayerSylow_image hnonab n hn S e hfour))
  exact (centralizerQuaternionImageEquiv hnonab n hn S e).trans eU.symm

theorem centralizerLiftedLayerSylow_card
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4))) :
    Nat.card (centralizerLiftedLayerSylow hnonab n hn S e hfour) = 2 * 2 ^ n := by
  let U := centralizerLiftedLayerSylow hnonab n hn S e hfour
  have hcard : Nat.card ((U : Subgroup (centralizerLiftedLayer n hn S e)).map
      (centralizerLiftedLayer n hn S e).subtype) = Nat.card U :=
    Subgroup.card_map_of_injective (K := (U : Subgroup (centralizerLiftedLayer n hn S e)))
      (f := (centralizerLiftedLayer n hn S e).subtype) Subtype.coe_injective
  rw [← hcard, centralizerLiftedLayerSylow_image hnonab n hn S e hfour]
  exact centralizerQuaternionImage_card hnonab n hn S e


end CFSG.Wreathed
