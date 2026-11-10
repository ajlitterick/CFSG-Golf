module

public import CFSG.Monster.B.TwoA.Amalgam.Data

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
open scoped Pointwise

theorem Qam_le_Eam
    (i : Fin 4) : Qam i ≤ Eam :=
  (Qam_le_Pc (j := i + 1) (by simp)).trans (Pc_le_Eam _)

theorem Bam_le_Eam :
    Bam ≤ Eam := (Bam_le_Pc 0).trans (Pc_le_Eam 0)

abbrev Chamber :
    Type := Quotient (QuotientGroup.rightRel (Bam.subgroupOf Eam))

@[expose] def chamberOf
    (g : Eam) : Chamber := Quotient.mk _ g

theorem chamberOf_eq_iff {g h : Eam} :
    chamberOf g = chamberOf h ↔ ((h * g⁻¹ : Eam) : Dfull) ∈ Bam :=
  Quotient.eq.trans ((QuotientGroup.rightRel_apply (s := Bam.subgroupOf Eam)).trans
    Subgroup.mem_subgroupOf)

theorem chamberOf_surjective :
    Function.Surjective chamberOf := Quotient.mk_surjective

theorem conj_mem_Qam_iff
    {i : Fin 4} {g₁ h₁ g₂ h₂ : Eam} (hg : ((g₂ * g₁⁻¹ : Eam) : Dfull) ∈ Bam)
    (hh : ((h₂ * h₁⁻¹ : Eam) : Dfull) ∈ Bam) :
    ((g₁ * h₁⁻¹ : Eam) : Dfull) ∈ Qam i ↔ ((g₂ * h₂⁻¹ : Eam) : Dfull) ∈ Qam i := by
  have hg' := Bam_le_Qam i hg
  have hh' := Bam_le_Qam i hh
  have e : ((g₂ * h₂⁻¹ : Eam) : Dfull) = ((g₂ * g₁⁻¹ : Eam) : Dfull) *
      ((g₁ * h₁⁻¹ : Eam) : Dfull) * ((h₂ * h₁⁻¹ : Eam) : Dfull)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  constructor
  · intro h
    exact (Qam i).mul_mem ((Qam i).mul_mem hg' h) ((Qam i).inv_mem hh')
  · intro h
    have h' : ((g₁ * h₁⁻¹ : Eam) : Dfull) = ((g₂ * g₁⁻¹ : Eam) : Dfull)⁻¹ *
        (((g₂ * g₁⁻¹ : Eam) : Dfull) * ((g₁ * h₁⁻¹ : Eam) : Dfull) *
          ((h₂ * h₁⁻¹ : Eam) : Dfull)⁻¹) * ((h₂ * h₁⁻¹ : Eam) : Dfull) := by group
    rw [h']
    exact (Qam i).mul_mem ((Qam i).mul_mem ((Qam i).inv_mem hg') h) hh'

@[expose] def chamberAdj
    (i : Fin 4) : Chamber → Chamber → Prop :=
  Quotient.lift₂ (fun g h : Eam => ((g * h⁻¹ : Eam) : Dfull) ∈ Qam i) fun _ _ _ _ hg hh =>
    propext (conj_mem_Qam_iff
      (Subgroup.mem_subgroupOf.1 ((QuotientGroup.rightRel_apply (s := Bam.subgroupOf Eam)).1 hg))
      (Subgroup.mem_subgroupOf.1 ((QuotientGroup.rightRel_apply (s := Bam.subgroupOf Eam)).1 hh)))

theorem chamberAdj_iff
    (i : Fin 4) (g h : Eam) :
    chamberAdj i (chamberOf g) (chamberOf h) ↔ ((g * h⁻¹ : Eam) : Dfull) ∈ Qam i := Iff.rfl


theorem chamberAdj_equivalence
    (i : Fin 4) : Equivalence (chamberAdj i) := by
  refine ⟨fun c => ?_, fun {c d} => ?_, fun {c d e} => ?_⟩
  · obtain ⟨g, rfl⟩ := chamberOf_surjective c
    rw [chamberAdj_iff, mul_inv_cancel]
    exact (Qam i).one_mem
  · obtain ⟨g, rfl⟩ := chamberOf_surjective c
    obtain ⟨h, rfl⟩ := chamberOf_surjective d
    rw [chamberAdj_iff, chamberAdj_iff]
    intro hgh
    have := (Qam i).inv_mem hgh
    rwa [← Subgroup.coe_inv, mul_inv_rev, inv_inv] at this
  · obtain ⟨g, rfl⟩ := chamberOf_surjective c
    obtain ⟨h, rfl⟩ := chamberOf_surjective d
    obtain ⟨k, rfl⟩ := chamberOf_surjective e
    rw [chamberAdj_iff, chamberAdj_iff, chamberAdj_iff]
    intro h1 h2
    have := (Qam i).mul_mem h1 h2
    rwa [← Subgroup.coe_mul, mul_assoc, inv_mul_cancel_left] at this

@[expose] def chamberMul
    (c : Chamber) (g : Eam) : Chamber :=
  Quotient.map' (· * g) (fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    rwa [mul_inv_rev, mul_assoc, mul_inv_cancel_left]) c

theorem chamberMul_chamberOf
    (h g : Eam) : chamberMul (chamberOf h) g = chamberOf (h * g) := rfl

theorem chamberMul_one
    (c : Chamber) : chamberMul c 1 = c := by
  obtain ⟨h, rfl⟩ := chamberOf_surjective c
  rw [chamberMul_chamberOf, mul_one]

theorem chamberMul_mul
    (c : Chamber) (g g' : Eam) :
    chamberMul c (g * g') = chamberMul (chamberMul c g) g' := by
  obtain ⟨h, rfl⟩ := chamberOf_surjective c
  rw [chamberMul_chamberOf, chamberMul_chamberOf, chamberMul_chamberOf, mul_assoc]

theorem chamberAdj_chamberMul
    (i : Fin 4) (c d : Chamber) (g : Eam) :
    chamberAdj i (chamberMul c g) (chamberMul d g) ↔ chamberAdj i c d := by
  obtain ⟨h, rfl⟩ := chamberOf_surjective c
  obtain ⟨k, rfl⟩ := chamberOf_surjective d
  rw [chamberMul_chamberOf, chamberMul_chamberOf, chamberAdj_iff, chamberAdj_iff, mul_inv_rev,
    mul_assoc, mul_inv_cancel_left]


end CFSG.Monster.B.TwoA.Amalgam
