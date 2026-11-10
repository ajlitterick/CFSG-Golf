module

public import CFSG.LocalAnalysis.ComponentInitial.PairedBinaryLinearThreeTensorOrbitsModels
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions
public import CFSG.Open.Defs

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits

open Module Matrix CFSG.ProperTwoGeneratedCore.PairedTensor
open CFSG.ProperTwoGeneratedCore.BinaryThreeSpace (Mat3 unitri unitriGL sylowT)
open scoped Pointwise

section Stab

variable {W : Type*} [AddCommMonoid W] [Module (ZMod 2) W]


end Stab

abbrev x₀ : N := ![0, 0, 1]


theorem det_eq_one (g : S) : (g : Mat3).det = 1 := by
  have h1 : Matrix.GeneralLinearGroup.det g = 1 := Subsingleton.elim _ _
  have h2 := congrArg (fun u : (ZMod 2)ˣ => (u : ZMod 2)) h1
  simpa using h2


@[expose] def IsUT (X : Mat3) : Prop :=
  X 1 0 = 0 ∧ X 2 0 = 0 ∧ X 2 1 = 0 ∧ X 0 0 = 1 ∧ X 1 1 = 1 ∧ X 2 2 = 1

instance (X : Mat3) : Decidable (IsUT X) := by
  unfold IsUT
  infer_instance

theorem isUT_unitri : ∀ a b c : ZMod 2, IsUT (unitri a b c) := by decide

theorem mem_U3_iff (g : S) : g ∈ U3 ↔ IsUT (g : Mat3) := by
  constructor
  · rintro ⟨a, b, c, rfl⟩
    exact isUT_unitri a b c
  · rintro ⟨h10, h20, h21, h00, h11, h22⟩
    refine ⟨(g : Mat3) 0 1, (g : Mat3) 0 2, (g : Mat3) 1 2, Units.ext ?_⟩
    change (g : Mat3) = unitri _ _ _
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unitri, h10, h20, h21, h00, h11, h22]

theorem card_U3 : Nat.card U3 = 8 := CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.card_sylowT

section Conj


end Conj

end CFSG.LocalAnalysis.ComponentInitial.PairedTensorOrbits
