module

public import CFSG.ClassicalInvolution.Q3.Q3WANoA1
public import CFSG.ClassicalInvolution.Q3.Q3YAbs

public section

namespace CFSG.ClassicalInvolution.Q3.Q3YS

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped MatrixGroups commutatorElement

section Group


theorem eq_of_inv_mul_mem_center {Y H : Type*} [Group Y] [Group H] [Group.IsPerfect Y]
    (a b : Y →* H) (hab : ∀ y, (a y)⁻¹ * b y ∈ Subgroup.center H) : a = b := by
  let χ : Y →* Subgroup.center H :=
    { toFun := fun y => ⟨(a y)⁻¹ * b y, hab y⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun y y' => by
        apply Subtype.ext
        have hc : (a y')⁻¹ * ((a y)⁻¹ * b y) = ((a y)⁻¹ * b y) * (a y')⁻¹ :=
          Subgroup.mem_center_iff.1 (hab y) ((a y')⁻¹)
        change (a (y * y'))⁻¹ * b (y * y') = (a y)⁻¹ * b y * ((a y')⁻¹ * b y')
        rw [map_mul, map_mul, _root_.mul_inv_rev]
        calc (a y')⁻¹ * (a y)⁻¹ * (b y * b y') = ((a y')⁻¹ * ((a y)⁻¹ * b y)) * b y' := by
              simp only [mul_assoc]
          _ = ((a y)⁻¹ * b y) * (a y')⁻¹ * b y' := by rw [hc]
          _ = (a y)⁻¹ * b y * ((a y')⁻¹ * b y') := by simp only [mul_assoc] }
  have hker : _root_.commutator Y ≤ χ.ker := Abelianization.commutator_subset_ker χ
  have htop : _root_.commutator Y = ⊤ := Group.IsPerfect.commutator_eq_top
  refine MonoidHom.ext fun y => ?_
  have hy : y ∈ χ.ker := hker (htop ▸ Subgroup.mem_top y)
  exact inv_mul_eq_one.1 (congrArg Subtype.val (MonoidHom.mem_ker.1 hy))

theorem mem_center_of_commutators_central {M : Type*} [Group M] [Group.IsPerfect M] {f : M}
    (hf : ∀ m : M, ⁅f, m⁆ ∈ Subgroup.center M) : f ∈ Subgroup.center M := by
  have h := eq_of_inv_mul_mem_center (MulAut.conj f).toMonoidHom (MonoidHom.id M) (fun y => by
    have := hf y⁻¹
    rw [commutatorElement_def] at this
    simpa [mul_assoc] using this)
  rw [Subgroup.mem_center_iff]
  intro g
  have := DFunLike.congr_fun h g
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
    MonoidHom.id_apply] at this
  calc g * f = f * g * f⁻¹ * f := by rw [this]
    _ = f * g := by simp


end Group

section Lie


variable {ι : Type} {X : Type} [Group X] {Φ : Set (Subgroup X)}


theorem central_of_central_in_range (D : LieSystemData3 ι X Φ) {i : ι} {x : X}
    (hxi : x ∈ (D.hom i).range) (hx : ∀ y ∈ (D.hom i).range, y * x = x * y) :
    ∀ g : X, g * x = x * g := by
  have hle : (⊤ : Subgroup X) ≤ Subgroup.centralizer ({x} : Set X) := by
    rw [← D.generate]
    refine iSup_le fun j => ?_
    by_cases hj : j = i
    · subst hj
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hx y hy)
    · rintro _ ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := hxi
      exact Subgroup.mem_centralizer_singleton_iff.mpr (D.commute j i hj b a)
  intro g
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))


end Lie

end CFSG.ClassicalInvolution.Q3.Q3YS
