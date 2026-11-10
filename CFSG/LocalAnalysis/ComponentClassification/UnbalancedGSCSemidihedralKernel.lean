module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCCentralTwoKernel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSABasic
public import CFSG.CharacterTheory.Semidihedral.CentralQuotients
public import CFSG.GroupTheory.QuaternionCentralizers

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedGS

namespace SemidihedralKernel

open Subgroup CentralTwoActionKernel


section General

variable {A : Type*} [Group A]

open CFSG.ComponentClassification.PerfectAutomorphisms in
theorem center_quotient_center_eq_bot [Group.IsPerfect A] : center (A ⧸ center A) = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have h : centerQuotientHom A (MulAut.conj x) = 1 := by
    refine MulEquiv.ext fun z => ?_
    induction z using QuotientGroup.induction_on with
    | H w =>
      change onCenterQuotient (MulAut.conj x) (QuotientGroup.mk' _ w) = QuotientGroup.mk' _ w
      rw [onCenterQuotient_apply_mk, MulAut.conj_apply, map_mul, map_mul, map_inv]
      have := mem_center_iff.mp hy (QuotientGroup.mk' _ w)
      change QuotientGroup.mk' _ w * QuotientGroup.mk' _ x = QuotientGroup.mk' _ x *
        QuotientGroup.mk' _ w at this
      rw [← this, mul_inv_cancel_right]
  have h1 := CFSG.LocalAnalysis.ComponentInitial.perfect_central_quotient_automorphism_faithful
    A (h.trans (map_one _).symm)
  have hx : x ∈ center A := (conj_eq_one_iff_mem_center x).mp h1
  rw [mem_bot]
  exact (QuotientGroup.eq_one_iff x).mpr hx

theorem quaternion_involution_unique {m : ℕ} [NeZero m] (x : QuaternionGroup m)
    (hx : orderOf x = 2) : x = QuaternionGroup.a (m : ZMod (2 * m)) := by
  cases x with
  | xa i =>
    rw [QuaternionGroup.orderOf_xa] at hx
    norm_num at hx
  | a i =>
    have h2 : QuaternionGroup.a i ^ 2 = 1 := hx ▸ pow_orderOf_eq_one _
    rw [pow_two, QuaternionGroup.a_mul_a, QuaternionGroup.one_def, QuaternionGroup.a.injEq,
      ← two_mul] at h2
    rcases (CFSG.GroupTheory.two_mul_eq_zero_iff_zmod i).mp h2 with rfl | rfl
    · rw [QuaternionGroup.a_zero, orderOf_one] at hx
      norm_num at hx
    · rfl

end General

variable {X : Type*} [Group X]

abbrev CentralQuot (L : Subgroup X) (O : Subgroup L) [O.Normal] :=
  (L ⧸ O) ⧸ center (L ⧸ O)


theorem sup_le_normalizer {L P : Subgroup X} (h : P ≤ normalizer (L : Set X)) :
    L ⊔ P ≤ normalizer (L : Set X) :=
  sup_le le_normalizer h


section Action

variable (L : Subgroup X) (O : Subgroup L) [O.Characteristic] (P : Subgroup X)
  [hP : Fact (P ≤ normalizer (L : Set X))]


theorem conj_mem_oddMap (g : normalizer (L : Set X)) {l : L} (hl : l ∈ O) :
    (g : X) * l * (g : X)⁻¹ ∈ O.map L.subtype := by
  have hchar := (Subgroup.characteristic_iff_map_eq.mp (inferInstance : O.Characteristic))
    (L.normalizerMonoidHom g)
  have hmem : L.normalizerMonoidHom g l ∈ O := by
    rw [← hchar]
    exact mem_map_of_mem _ hl
  exact ⟨_, hmem, rfl⟩

instance oddMap_normal : ((O.map L.subtype).subgroupOf (L ⊔ P)).Normal := by
  refine ⟨fun x hx h => ?_⟩
  rw [mem_subgroupOf] at hx ⊢
  obtain ⟨l, hl, hlx⟩ := hx
  have := conj_mem_oddMap L O ⟨h, sup_le_normalizer hP.out h.2⟩ hl
  simp only [coe_mul, coe_inv]
  rw [← hlx]
  exact this

end Action


end SemidihedralKernel

open Subgroup CentralTwoActionKernel SemidihedralKernel CFSG.Semidihedral CFSG.Open


end CFSG.ComponentClassification.UnbalancedGS
