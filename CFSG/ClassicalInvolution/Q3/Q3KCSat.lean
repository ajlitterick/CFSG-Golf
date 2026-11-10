module

public import CFSG.ClassicalInvolution.Q3.Q3KCBoot
public import CFSG.ClassicalInvolution.Balance.BootstrapUntouched
import CFSG.ClassicalInvolution.Q3.Q3NHVertex

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3KC

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Q3.Q3NG


section Defs

variable {G : Type} [Group G]


end Defs

section Abstract

variable {X : Type} [Group X] {ι : Type} {Φ : Set (Subgroup X)}

theorem le_range_of_not_centralizes (D : LieSystemData3 ι X Φ) {k : ι} {M : Subgroup X}
    (hM : M ∈ Φ) {m : X} (hm : m ∈ M) (hnc : ¬ ∀ q ∈ (D.hom k).range, m * q = q * m) :
    M ≤ (D.hom k).range :=
  CFSG.ClassicalInvolution.Q3.Q3NH.le_range_of_not_centralizes' D hM hm hnc

end Abstract

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {A : Subgroup G}

theorem exists_lift_centralizer_group {Y : Subgroup G} (hA : IsElemAbelian 2 A) (hAY : A ≤ Y)
    {q : ↥Y ⧸ classicalInvolutionOddCore ↥Y}
    (hq : ∀ (f : G) (hf : f ∈ A), QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)
      ⟨f, hAY hf⟩ * q = q * QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨f, hAY hf⟩) :
    ∃ y : ↥Y, y ∈ Subgroup.centralizer ((A.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) y = q := by
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  set E : Subgroup ↥Y := A.subgroupOf Y with hE
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx =>
    Subtype.ext (Q3C.elem_sq hA (Subgroup.mem_subgroupOf.mp hx))
  have hnorm : E ≤ Subgroup.normalizer ((⊤ : Subgroup ↥Y) : Set ↥Y) := fun x _ =>
    (Subgroup.mem_normalizer_iff).mpr fun h => by simp
  have key := map_inf_centralizer_eq π (Q3Y2.odd_card_ker_mk Y) E ⊤
    (isPGroup_two_of_sq_eq_one hE2) hnorm
  have hqmem : q ∈ (⊤ : Subgroup ↥Y).map π ⊓ Subgroup.centralizer (E.map π : Set _) := by
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
    · obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ q
      exact ⟨y, trivial, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact hq x (Subgroup.mem_subgroupOf.mp hx)
  rw [← key] at hqmem
  obtain ⟨y, ⟨-, hyE⟩, hyq⟩ := hqmem
  exact ⟨y, hyE, hyq⟩

theorem exists_involution_lift_group {Y : Subgroup G} (hA : IsElemAbelian 2 A) (hAY : A ≤ Y)
    {z : G} (hzY : z ∈ Y) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hcomm : ∀ (f : G) (hf : f ∈ A), QuotientGroup.mk' (classicalInvolutionOddCore ↥Y)
        ⟨f, hAY hf⟩ * QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨z, hzY⟩ =
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨z, hzY⟩ *
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨f, hAY hf⟩) :
    ∃ (w : G) (hw : w ∈ Y), w ∈ Subgroup.centralizer (A : Set G) ∧ w * w = 1 ∧
      QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨w, hw⟩ =
        QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) ⟨z, hzY⟩ := by
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥Y) with hπ
  obtain ⟨y, hyE, hyq⟩ := exists_lift_centralizer_group hA hAY (q := π ⟨z, hzY⟩) hcomm
  have hker : Odd (Nat.card π.ker) := Q3Y2.odd_card_ker_mk Y
  have hzb1 : π ⟨z, hzY⟩ ≠ 1 := Q3Y.mk_ne_one_of_involution Y hzY hz2 hz1
  have hzb2 : π ⟨z, hzY⟩ ^ 2 = 1 := by
    rw [pow_two, ← map_mul]
    have : (⟨z, hzY⟩ : ↥Y) * ⟨z, hzY⟩ = 1 := Subtype.ext hz2
    rw [this, map_one]
  have hord : orderOf (π ⟨z, hzY⟩) = 2 := orderOf_eq_prime hzb2 hzb1
  have hy2 : y ^ 2 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hyq]
    exact hzb2
  have hodd : Odd (orderOf (y ^ 2)) := hker.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hy2)
  have hdvd : 2 ∣ orderOf y := by
    have := orderOf_map_dvd π y
    rw [hyq, hord] at this
    exact this
  obtain ⟨m, hm⟩ := hdvd
  have hgm : orderOf (y ^ 2) = m := by
    rw [orderOf_pow_of_dvd (by norm_num) ⟨m, hm⟩, hm]
    omega
  rw [hgm] at hodd
  refine ⟨((y ^ m : ↥Y) : G), (y ^ m).2, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hge : y ^ m ∈ Subgroup.centralizer ((A.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) :=
      Subgroup.pow_mem _ hyE m
    have := Subgroup.mem_centralizer_iff.mp hge ⟨e, hAY he⟩ (Subgroup.mem_subgroupOf.mpr he)
    exact congrArg Subtype.val this
  · have : y ^ m * y ^ m = 1 := by
      rw [← pow_add, ← two_mul, ← hm]
      exact pow_orderOf_eq_one y
    exact congrArg Subtype.val this
  · obtain ⟨k, hk⟩ := hodd
    show π (y ^ m) = π ⟨z, hzY⟩
    rw [map_pow, hyq, hk, pow_succ, pow_mul, hzb2, one_pow, one_mul]

end Lift

section Cover


end Cover

section Generation


end Generation


end CFSG.ClassicalInvolution.Q3.Q3KC
