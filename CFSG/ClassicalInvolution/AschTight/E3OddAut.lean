module

public import CFSG.ClassicalInvolution.AschTight.CSM

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups

theorem mem_center_of_commutator_mem_center {L : Type} [Group L] [Group.IsPerfect L] {x : L}
    (h : ∀ y : L, y * x * y⁻¹ * x⁻¹ ∈ Subgroup.center L) : x ∈ Subgroup.center L := by
  let _ : CommGroup (Subgroup.center L) :=
    { (inferInstance : Group (Subgroup.center L)) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a) }
  let φ : L →* Subgroup.center L :=
    { toFun := fun y => ⟨y * x * y⁻¹ * x⁻¹, h y⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun y y' => by
        apply Subtype.ext
        change y * y' * x * (y * y')⁻¹ * x⁻¹ = (y * x * y⁻¹ * x⁻¹) * (y' * x * y'⁻¹ * x⁻¹)
        rw [commutator_mul (Subgroup.mem_center_iff.mp (h y') y)]
        exact Subgroup.mem_center_iff.mp (h y) _ }
  rw [Subgroup.mem_center_iff]
  intro y
  have h1 : y * x * y⁻¹ * x⁻¹ = 1 := congrArg Subtype.val (eq_one_of_perfect φ y)
  calc y * x = y * x * y⁻¹ * x⁻¹ * (x * y) := by group
    _ = x * y := by rw [h1, one_mul]


section PSL2

variable {L : Type} [Group L] {F : Type} [Field F]


end PSL2

section Conj

variable {G : Type} [Group G]

@[expose] def normalizerConj (K : Subgroup G) : Subgroup.normalizer (K : Set G) →* MulAut K where
  toFun n :=
    { toFun := fun k => ⟨n * k * (n : G)⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 k).mp k.2⟩
      invFun := fun k => ⟨(n : G)⁻¹ * k * n, by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ n.2) k).mp k.2
        simpa using this⟩
      left_inv := fun k => Subtype.ext (by simp [mul_assoc])
      right_inv := fun k => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun k k' => Subtype.ext (by simp [mul_assoc]) }
  map_one' := by
    ext k
    simp
  map_mul' n n' := by
    ext k
    simp [mul_assoc]

theorem normalizerConj_apply_coe (K : Subgroup G) (n : Subgroup.normalizer (K : Set G))
    (k : K) : ((normalizerConj K n k : K) : G) = n * k * (n : G)⁻¹ :=
  rfl

@[expose] def centerQuotientAut (L : Type) [Group L] :
    MulAut L →* MulAut (L ⧸ Subgroup.center L) where
  toFun α := QuotientGroup.congr (Subgroup.center L) (Subgroup.center L) α
    (Subgroup.characteristic_iff_map_eq.mp inferInstance α)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' α β := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem centerQuotientAut_mk (L : Type) [Group L] (α : MulAut L) (x : L) :
    centerQuotientAut L α (QuotientGroup.mk x) = QuotientGroup.mk (α x) :=
  rfl

end Conj

section Action


end Action

end CFSG.ClassicalInvolution.Disconnected.AschTight
