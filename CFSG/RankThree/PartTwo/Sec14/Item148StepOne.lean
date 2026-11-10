module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepKFacts
import CFSG.RankThree.PartTwo.Sec14.Item148Proof
public import CFSG.RankThree.PartTwo.Sec14.Item148Steps

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem innerOn148_of_pow_three {Γ : Type*} [Group Γ] {X : Subgroup Γ} {g : Γ}
    (hg : g ∈ Subgroup.normalizer (X : Set Γ)) (hg3 : g ^ 3 = 1)
    (hX : ∀ σ : MulAut X, σ ^ 3 = 1 → σ ∈ (MulAut.conj : X →* MulAut X).range) :
    InnerOn148 X g := by
  set σ := X.normalizerMonoidHom ⟨g, hg⟩ with hσ
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨g, hg⟩ : Subgroup.normalizer (X : Set Γ)) ^ 3 = 1 := Subtype.ext (by simpa using hg3)
    rw [this, map_one]
  obtain ⟨x, hx⟩ := hX σ hσ3
  refine ⟨x, x.2, fun y hy => ?_⟩
  have h := congrArg (fun τ : MulAut X => ((τ ⟨y, hy⟩ : X) : Γ)) hx
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
  rw [h]
  rfl

variable {G : Type} [Group G] [Finite G]

section Lemmas

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

omit [Finite G] in
theorem isPerfect_img148 {J : Subgroup G} (hJM : J ≤ Y ⊔ A) [Group.IsPerfect J] :
    Group.IsPerfect ↥(img148 A Y J) := by
  have : Group.IsPerfect ↥(J.subgroupOf (Y ⊔ A)) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJM).symm.toMonoidHom)
      (MulEquiv.surjective _)
  exact Group.IsPerfect.map (H := J.subgroupOf (Y ⊔ A)) (QuotientGroup.mk' (ker148 A Y))

omit [Finite G] in
theorem mem_sectionCentralizer_of_alpha148 {J : Subgroup G} (hJM : J ≤ Y ⊔ A) {a : G}
    (ha : a ∈ A)
    (hc : alpha148 A Y a ha ∈ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y))) :
    a ∈ Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) := by
  refine ⟨ha, fun x hx => ?_⟩
  have hxM : x ∈ Y ⊔ A := hJM hx
  have haM : a ∈ Y ⊔ A := Subgroup.mem_sup_right ha
  have hmem : a * x * a⁻¹ * x⁻¹ ∈ Y ⊔ A :=
    (Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem ((Y ⊔ A).mul_mem haM hxM) ((Y ⊔ A).inv_mem haM))
      ((Y ⊔ A).inv_mem hxM)
  refine (mk'_ker148_eq_one_iff (g := ⟨_, hmem⟩)).mp ?_
  have hxb : QuotientGroup.mk' (ker148 A Y) ⟨x, hxM⟩ ∈ img148 A Y J :=
    mem_img148_iff.mpr ⟨x, hxM, hx, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp hc _ hxb
  have e1 : QuotientGroup.mk' (ker148 A Y) ⟨_, hmem⟩ =
      alpha148 A Y a ha * QuotientGroup.mk' (ker148 A Y) ⟨x, hxM⟩ * (alpha148 A Y a ha)⁻¹ *
        (QuotientGroup.mk' (ker148 A Y) ⟨x, hxM⟩)⁻¹ := by
    rw [alpha148_eq_mk', ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [e1, ← hcomm]
  group

omit [Finite G] in
theorem img148_inf_centralizer_eq {J K : Subgroup G} (hKM : K ≤ Y ⊔ A) {e : G} (he : e ∈ A)
    (hKe : K ≤ Subgroup.centralizer {e})
    (hsec : Late.sectionCentralizer A K (pPrimeCoreOf 3 Y) = (Subgroup.zpowers e : Set G))
    (hKJ : img148 A Y K = img148 A Y J) :
    img148 A Y A ⊓ Subgroup.centralizer (img148 A Y J : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) =
      Subgroup.zpowers (alpha148 A Y e he) := by
  apply le_antisymm
  · rintro x ⟨hxA, hxc⟩
    obtain ⟨a, haM, haA, rfl⟩ := mem_img148_iff.mp hxA
    have hc : alpha148 A Y a haA ∈
        Subgroup.centralizer (img148 A Y K : Set (↥(Y ⊔ A) ⧸ ker148 A Y)) := by
      rw [hKJ]
      exact hxc
    have hsa := mem_sectionCentralizer_of_alpha148 hKM haA hc
    rw [hsec] at hsa
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hsa
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [alpha148_eq_mk', ← map_zpow]
    congr 1
    exact Subtype.ext (by simpa using hk)
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨alpha148_mem_img148 he, ?_⟩
    rw [← hKJ, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, hkM, hkK, rfl⟩ := mem_img148_iff.mp hy
    rw [alpha148_eq_mk', ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hKe hkK))

end Lemmas

section Pointwise

variable {A Y : Subgroup G} [(ker148 A Y).Normal]

omit [Finite G] in
theorem alpha148_pow_three (hA3 : ∀ a ∈ A, a ^ 3 = 1) {a : G} (ha : a ∈ A) :
    alpha148 A Y a ha ^ 3 = 1 := by
  rw [← alpha148_pow ha]
  simp only [hA3 a ha]
  rfl

omit [Finite G] in
theorem alpha148_comm (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) {a b : G} (ha : a ∈ A)
    (hb : b ∈ A) :
    alpha148 A Y a ha * alpha148 A Y b hb = alpha148 A Y b hb * alpha148 A Y a ha := by
  rw [← alpha148_mul ha hb, ← alpha148_mul hb ha]
  congr 1
  exact hAc a ha b hb

omit [Finite G] [(ker148 A Y).Normal] in
theorem sectionCentralizer_subset_of_le {J K : Subgroup G} {e : G} (hKJ : K ≤ J)
    (hsec : Late.sectionCentralizer A K (pPrimeCoreOf 3 Y) = (Subgroup.zpowers e : Set G)) :
    Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) ⊆ (Subgroup.zpowers e : Set G) := by
  intro a ha
  rw [← hsec]
  exact ⟨ha.1, fun x hx => ha.2 x (hKJ hx)⟩

theorem eq_zpowers_sup_inf_of_inner148 (hI : KF148Inner) (hAF : A ∈ partTwoF G)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {J : Subgroup G} (hJY : J ≤ Y)
    (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {e : G} (he : e ∈ A)
    (hCJ : Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) ⊆ (Subgroup.zpowers e : Set G))
    (hX : Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
      Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 7)) ∨
      Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
      Nonempty (↥(img148 A Y J) ≃* CFSG.Blueprint.NativeSporadic.M12) ∨
      Nonempty (↥(img148 A Y J) ≃* alternatingGroup (Fin 10))) :
    A = Subgroup.zpowers e ⊔ (A ⊓ J) := by
  obtain ⟨hZ, haut⟩ := hI _ hX
  refine eq_zpowers_sup_inf_of_innerOn hAF hAY hJY hAJ he hZ hCJ fun a ha => ⟨0, ?_⟩
  rw [pow_zero, mul_one]
  exact innerOn148_of_pow_three (img148_le_normalizer hAJ (alpha148_mem_img148 ha))
    (alpha148_pow_three hAF.1.2 ha) haut


theorem eq_zpowers_sup_inf_of_field148 (hF : KF148Field)
    (hAF : A ∈ partTwoF G) (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {J : Subgroup G}
    (hJ : J ∈ thetaComponentsIn Y) (hAJ : A ≤ Subgroup.normalizer (J : Set G)) {e : G}
    (he : e ∈ A)
    (hCJ : Late.sectionCentralizer A J (pPrimeCoreOf 3 Y) ⊆ (Subgroup.zpowers e : Set G))
    {K : Subgroup G} (hField : Lift148Field A Y e he K J) :
    A = Subgroup.zpowers e ⊔ (A ⊓ J) := by
  have hC := kf148CenterL3
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAF.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hJY : J ≤ Y := le_of_mem_thetaComponentsIn hJ
  have : Group.IsPerfect J := isPerfect_of_mem_thetaComponentsIn hJ
  have hJp : Group.IsPerfect ↥(img148 A Y J) := isPerfect_img148 (hJY.trans le_sup_left)
  obtain ⟨n, hn, -, hJn, hkind⟩ := hField
  have hZ : Subgroup.center ↥(img148 A Y J) = ⊥ :=
    hC _ hJp (Or.inl ⟨2, 3 * n, inferInstance, by omega, hJn⟩)
  refine eq_zpowers_sup_inf_of_innerOn hAF hAY hJY hAJ he hZ hCJ fun a ha => ?_
  exact hF _ (img148 A Y J) n (alpha148 A Y e he) (alpha148 A Y a ha) hn hJn hkind
    (alpha148_pow_three hA3 he) (img148_le_normalizer hAJ (alpha148_mem_img148 ha))
    (alpha148_pow_three hA3 ha) (alpha148_comm hAc he ha)

end Pointwise

section Step


end Step

end CFSG.RankThree.PartTwo.Sec14
