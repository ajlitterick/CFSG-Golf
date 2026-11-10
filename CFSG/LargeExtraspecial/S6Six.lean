module

public import CFSG.LargeExtraspecial.S4FiveW

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S6

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S) in
@[expose] noncomputable def Q1 (t : S.O) : Subgroup G :=
  S.clPre (fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt))


theorem coe_mul_self {t : S.O} (htt : t * t = 1) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) = 1 :=
  congrArg Subtype.val htt

theorem orthogonal_fixSpace {t : S.O} (htt : t * t = 1) :
    LinearMap.BilinForm.orthogonal S.q.polarBilin (fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) =
      commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  rw [fixSpace_eq_orthogonal_commSpace S.q_nondegenerate t.2 (coe_mul_self htt),
    LinearMap.BilinForm.orthogonal_orthogonal S.q_nondegenerate S.polarBilin_isRefl]


variable (S) in
@[expose] noncomputable def chiU (t : S.O) :
    (S.Qt ⧸ fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) ≃ₗ[ZMod 2]
      commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  LinearMap.quotKerEquivRange _


theorem apply_mem_commSpace_of_commute {t r : S.O} (hr : r * t = t * r) {v : S.Qt}
    (hv : v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    (r : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
  refine mem_commSpace.mpr ⟨(r : S.Qt ≃ₗ[ZMod 2] S.Qt) w, ?_⟩
  rw [map_sub, ← coe_mul_apply, ← coe_mul_apply, hr]

variable (S) in
@[expose] noncomputable def Tt (g : G) (t : S.O) : Submodule (ZMod 2) S.Qt :=
  (Wt S g t).map (((t : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)

theorem mem_Tt {t : S.O} {v : S.Qt} :
    v ∈ Tt S g t ↔ ∃ w ∈ Wt S g t, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w = v := by
  simp [Tt]

theorem sub_mem_Tt {t : S.O} {w : S.Qt} (hw : w ∈ Wt S g t) :
    (t : S.Qt ≃ₗ[ZMod 2] S.Qt) w - w ∈ Tt S g t :=
  mem_Tt.mpr ⟨w, hw, rfl⟩

theorem Tt_le_commSpace {t : S.O} : Tt S g t ≤ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  intro v hv
  obtain ⟨w, -, rfl⟩ := mem_Tt.mp hv
  exact sub_mem_commSpace _ w

theorem apply_mem_Tt (H : Hyp4 S g) {t x : S.O} (hx : x ∈ Rbar S g t) {v : S.Qt}
    (hv : v ∈ Tt S g t) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ Tt S g t := by
  obtain ⟨w, hw, rfl⟩ := mem_Tt.mp hv
  refine mem_Tt.mpr ⟨_, apply_mem_Wt H hx hw, ?_⟩
  rw [map_sub, ← coe_mul_apply, ← coe_mul_apply, commute_of_mem_Rbar H.conj_mem hx]

theorem Vt_le_commSpace (H : Hyp4 S g) {t : S.O} (ht1 : t ≠ 1) :
    Vt S g t ≤ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
  have hne : commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≠ ⊥ := by
    intro h
    have := one_le_finrank_commSpace (g := (t : S.Qt ≃ₗ[ZMod 2] S.Qt))
      (fun h1 => ht1 (Subtype.ext h1))
    rw [h, finrank_bot] at this
    omega
  exact Vt_le_of_invariant H hne fun x hx v hv => apply_mem_commSpace_t H hx hv

theorem fixSpace_le_Wt (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) :
    fixSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ≤ Wt S g t := by
  intro v hv
  rw [fixSpace_eq_orthogonal_commSpace S.q_nondegenerate t.2
    (coe_mul_self (mul_self_of_mem_Lbar S H.conj_mem ht)),
    LinearMap.BilinForm.mem_orthogonal_iff] at hv
  refine mem_Wt.mpr fun u hu => ?_
  have := hv u (Vt_le_commSpace H ht1 hu)
  rwa [polarBilin_apply_apply] at this

end CFSG.LargeExtraspecial.S6
