module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTablesSp6
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCShortRoot
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.ClassicalGroups.Symplectic.Perfect

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_equiv_diagonal)
open CFSG.Quasithin (perfectCore derivedSeriesOf)
open scoped MatrixGroups commutatorElement


theorem commutator_range_eq_of_isPerfect {G H : Type*} [Group G] [Group H] [Group.IsPerfect G]
    (f : G →* H) : ⁅f.range, f.range⁆ = f.range := by
  rw [MonoidHom.range_eq_map, ← map_commutator, ← commutator_def,
    Group.IsPerfect.commutator_eq_top]

section Rows

variable {K : Type} [Field K] {n : ℕ}

theorem mul_apply_of_row {X Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} {a : Fin n ⊕ Fin n}
    (hX : ∀ c, c ≠ a → X a c = 0) (b : Fin n ⊕ Fin n) : (X * Y) a b = X a a * Y a b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a (fun c _ hc => by rw [hX c hc, zero_mul])
    (fun h => absurd (Finset.mem_univ a) h)]

theorem mul_apply_of_col {X Y : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} {a : Fin n ⊕ Fin n}
    (hY : ∀ c, c ≠ a → Y c a = 0) (b : Fin n ⊕ Fin n) : (X * Y) b a = X b a * Y a a := by
  rw [Matrix.mul_apply, Finset.sum_eq_single a (fun c _ hc => by rw [hY c hc, mul_zero])
    (fun h => absurd (Finset.mem_univ a) h)]

theorem commutator_le_suppGroup {B : Set (Fin n ⊕ Fin n)} {H : Subgroup (StatedSp n K)}
    (hH : ∀ x ∈ H, ∀ a ∉ B, ∀ b, b ≠ a → mat n K x a b = 0 ∧ mat n K x b a = 0) :
    ⁅H, H⁆ ≤ suppGroup B := by
  rw [Subgroup.commutator_le]
  intro g hg h hh
  have hrow : ∀ x ∈ H, ∀ y : StatedSp n K, ∀ a ∉ B, ∀ b,
      mat n K (x * y) a b = mat n K x a a * mat n K y a b := fun x hx y a ha b => by
    rw [map_mul]
    exact mul_apply_of_row (fun c hc => (hH x hx a ha c hc).1) b
  have hcol : ∀ x : StatedSp n K, ∀ y ∈ H, ∀ a ∉ B, ∀ b,
      mat n K (x * y) b a = mat n K x b a * mat n K y a a := fun x y hy a ha b => by
    rw [map_mul]
    exact mul_apply_of_col (fun c hc => (hH y hy a ha c hc).2) b
  have hinv : ∀ x ∈ H, ∀ a ∉ B, mat n K x a a * mat n K x⁻¹ a a = 1 := fun x hx a ha => by
    rw [← hrow x hx x⁻¹ a ha a, mul_inv_cancel, map_one, Matrix.one_apply_eq]
  have hc : ⁅g, h⁆ = g * h * g⁻¹ * h⁻¹ := commutatorElement_def g h
  have hghg : g * h * g⁻¹ ∈ H := mul_mem (mul_mem hg hh) (inv_mem hg)
  have hdiag : ∀ a ∉ B, mat n K g a a * mat n K h a a * mat n K g⁻¹ a a * mat n K h⁻¹ a a = 1 :=
    fun a ha => by
    calc _ = (mat n K g a a * mat n K g⁻¹ a a) * (mat n K h a a * mat n K h⁻¹ a a) := by ring
      _ = 1 := by rw [hinv g hg a ha, hinv h hh a ha, one_mul]
  have hr : ∀ a ∉ B, ∀ b, mat n K ⁅g, h⁆ a b =
      mat n K g a a * mat n K h a a * mat n K g⁻¹ a a * mat n K h⁻¹ a b := fun a ha b => by
    rw [hc, hrow _ hghg _ a ha, hrow _ (mul_mem hg hh) _ a ha, hrow _ hg _ a ha]
  have hcl : ∀ a ∉ B, ∀ b, mat n K ⁅g, h⁆ b a =
      mat n K g b a * mat n K h a a * mat n K g⁻¹ a a * mat n K h⁻¹ a a := fun a ha b => by
    rw [hc, hcol _ _ (inv_mem hh) a ha, hcol _ _ (inv_mem hg) a ha, hcol _ _ hh a ha]
  intro r t hrt
  by_cases hrB : r ∈ B
  · have htB : t ∉ B := fun htB => hrt ⟨hrB, htB⟩
    rw [hcl t htB r]
    by_cases hrt' : r = t
    · subst hrt'
      exact absurd hrB htB
    · rw [(hH g hg t htB r hrt').2, zero_mul, zero_mul, zero_mul, Matrix.one_apply_ne hrt']
  · rw [hr r hrB t]
    by_cases hrt' : t = r
    · subst hrt'
      rw [hdiag t hrB, Matrix.one_apply_eq]
    · rw [(hH _ (inv_mem hh) r hrB t hrt').1, mul_zero, Matrix.one_apply_ne (Ne.symm hrt')]

end Rows

section Weights

variable {F : Type} [Field F]

@[expose] def sp6Weight (t : Fin 3 → Fˣ) : Fin 3 ⊕ Fin 3 → F :=
  Sum.elim (fun i => (t i : F)) (fun i => (((t i)⁻¹ : Fˣ) : F))

@[simp] theorem sp6Weight_inl (t : Fin 3 → Fˣ) (i : Fin 3) :
    sp6Weight t (Sum.inl i) = (t i : F) := rfl

@[simp] theorem sp6Weight_inr (t : Fin 3 → Fˣ) (i : Fin 3) :
    sp6Weight t (Sum.inr i) = (((t i)⁻¹ : Fˣ) : F) := rfl

theorem mat_sp6Diag (t : Fin 3 → Fˣ) : mat 3 F (sp6Diag F t) = Matrix.diagonal (sp6Weight t) :=
  mat_equiv_diagonal t


end Weights

section Separate

variable {F : Type} [Field F]


theorem sp6ParamA_eq (a : Fˣ) : sp6ParamA F a = Pi.mulSingle 0 a := rfl

theorem sp6ParamM2_eq (p : Fˣ × Fˣ) : sp6ParamM2 F p = Pi.mulSingle 0 p.1 * Pi.mulSingle 1 p.2 :=
  rfl

theorem sp6ParamM3_eq (p : Fˣ × Fˣ) :
    sp6ParamM3 F p = Pi.mulSingle 0 p.1 * (Pi.mulSingle 1 p.2 * Pi.mulSingle 2 p.2) :=
  rfl


end Separate

section Perfect


end Perfect

section CaseA


end CaseA

section CaseM2


end CaseM2

section CaseM3


end CaseM3


end CFSG.SeitzReduction.F4Pilot
