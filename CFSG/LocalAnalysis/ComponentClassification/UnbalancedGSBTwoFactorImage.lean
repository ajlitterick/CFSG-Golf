module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup
open scoped commutatorElement


theorem commutator_range_eq_of_perfect {G H : Type*} [Group G] [Group H] (hG : Group.IsPerfect G)
    (f : G →* H) : ⁅f.range, f.range⁆ = f.range := by
  rw [MonoidHom.range_eq_map, ← map_commutator, ← _root_.commutator_def,
    Group.isPerfect_def.mp hG]

theorem isPerfect_of_commutator_eq {G : Type*} [Group G] {K : Subgroup G} (hK : ⁅K, K⁆ = K) :
    Group.IsPerfect K := by
  rw [Group.isPerfect_def, _root_.commutator_def]
  apply map_injective K.subtype_injective
  rw [map_commutator, ← MonoidHom.range_eq_map, range_subtype, hK]


theorem mem_zpowers_iff_eq_one_or_eq {G : Type*} [Group G] {g x : G} (hg : orderOf g = 2) :
    x ∈ zpowers g ↔ x = 1 ∨ x = g := by
  rw [mem_zpowers_iff]
  constructor
  · rintro ⟨k, rfl⟩
    rw [← zpow_mod_orderOf, hg]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [Nat.cast_ofNat, h, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h, zpow_one]
  · rintro (h | h)
    · rw [h]
      exact ⟨0, zpow_zero g⟩
    · rw [h]
      exact ⟨1, zpow_one g⟩

section TwoFactor

variable (A : Type*) [Group A]

@[expose] def centerDiagonal : Subgroup (A × A) where
  carrier := {x | x.1 ∈ center A ∧ x.1 = x.2}
  mul_mem' := by
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨ha, hab⟩ ⟨hc, hcd⟩
    exact ⟨mul_mem ha hc, by simp only [Prod.mk_mul_mk] at *; rw [hab, hcd]⟩
  one_mem' := ⟨one_mem _, rfl⟩
  inv_mem' := by
    rintro ⟨a, b⟩ ⟨ha, hab⟩
    exact ⟨inv_mem ha, by simp only [Prod.inv_mk] at *; rw [hab]⟩

variable {A}


variable (A)

theorem centerDiagonal_le_center : centerDiagonal A ≤ center (A × A) := by
  rintro ⟨a, b⟩ ⟨ha, hab⟩
  simp only at ha hab
  subst hab
  rw [mem_center_iff]
  rintro ⟨c, d⟩
  ext
  · exact mem_center_iff.mp ha c
  · exact mem_center_iff.mp ha d

instance centerDiagonal_normal : (centerDiagonal A).Normal := by
  refine ⟨fun n hn g => ?_⟩
  have hc := mem_center_iff.mp (centerDiagonal_le_center A hn) g
  rw [hc, mul_inv_cancel_right]
  exact hn


variable {A}


theorem mk_eq_one_iff_centerDiagonal (x y : A) :
    ((x, y) : (A × A) ⧸ centerDiagonal A) = 1 ↔ x ∈ center A ∧ x = y :=
  QuotientGroup.eq_one_iff _

section Involution

variable {z : A}


@[expose] def diagonalHom (α : MulAut A) : A →* (A × A) ⧸ centerDiagonal A :=
  (QuotientGroup.mk' (centerDiagonal A)).comp ((MonoidHom.id A).prod α.toMonoidHom)


theorem inl_injective :
    Function.Injective ((QuotientGroup.mk' (centerDiagonal A)).comp (MonoidHom.inl A A)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  exact ((mk_eq_one_iff_centerDiagonal x 1).mp hx).2

theorem inr_injective :
    Function.Injective ((QuotientGroup.mk' (centerDiagonal A)).comp (MonoidHom.inr A A)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  exact ((mk_eq_one_iff_centerDiagonal 1 x).mp hx).2.symm


end Involution

theorem normal_le_center_of_ne_top [Finite A] (hperf : Group.IsPerfect A)
    [IsSimpleGroup (A ⧸ center A)] (N : Subgroup A) (hN : N.Normal) (hNtop : N ≠ ⊤) :
    N ≤ center A := by
  have hM : (N.map (QuotientGroup.mk' (center A))).Normal :=
    hN.map _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (center A))) with
    h | h
  · rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · exfalso
    apply hNtop
    have hsup : N ⊔ center A = ⊤ := by
      rw [← QuotientGroup.ker_mk' (center A), ← comap_map_eq, h, comap_top]
    have hcomm : ∀ a b : A ⧸ N, a * b = b * a := by
      intro a b
      induction a using QuotientGroup.induction_on with | H x => ?_
      induction b using QuotientGroup.induction_on with | H y => ?_
      have hx : x ∈ N ⊔ center A := hsup ▸ mem_top x
      have hy : y ∈ N ⊔ center A := hsup ▸ mem_top y
      rw [← SetLike.mem_coe, mul_normal N (center A)] at hx hy
      obtain ⟨n, hn, w, hw, rfl⟩ := Set.mem_mul.mp hx
      obtain ⟨n', hn', w', hw', rfl⟩ := Set.mem_mul.mp hy
      have h1 : ((n * w : A) : A ⧸ N) = (w : A ⧸ N) := by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
      have h2 : ((n' * w' : A) : A ⧸ N) = (w' : A ⧸ N) := by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n').mpr hn', one_mul]
      rw [h1, h2, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, mem_center_iff.mp hw' w]
    have hle : commutator A ≤ N := by
      rw [_root_.commutator_def, commutator_le]
      intro a _ b _
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    rw [Group.isPerfect_def.mp hperf] at hle
    exact top_unique hle

end TwoFactor


end CFSG.ComponentClassification.UnbalancedGS
