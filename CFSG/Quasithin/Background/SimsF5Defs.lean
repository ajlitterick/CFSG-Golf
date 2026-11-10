module

public import CFSG.Milestones.ASVolI.F4
public import CFSG.Quasithin.Recognition.UniquenessSystemTriangulation
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Background.F3
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3

public section

namespace CFSG.Quasithin.SimsF5

noncomputable section

open scoped Pointwise
open Matrix CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF

abbrev GL6 : Type := Matrix.GeneralLinearGroup (Fin 6) (ZMod 3)

abbrev V6 : Type := Fin 6 → ZMod 3

abbrev Sub6 : Type := Submodule (ZMod 3) V6

@[expose] def qV (v : V6) : ZMod 3 := v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 + v 4 ^ 2 - v 5 ^ 2

@[expose] def bil (u v : V6) : ZMod 3 := qV (u + v) - qV u - qV v

@[expose] def xvec (i : Fin 6) : V6 := Pi.single i 1


@[expose] def Iset : Finset (Fin 6) := {0, 1, 2, 3, 4}


@[expose] def OVq : Subgroup GL6 := CFSG.MatrixModel.isometryCore qV

@[expose] def MDot : Subgroup GL6 := StatedOmega qV

@[expose] def eJd (J : Finset (Fin 6)) : Fin 6 → ZMod 3 := fun i => if i ∈ J then -1 else 1

theorem eJ_mat_sq (J : Finset (Fin 6)) :
    Matrix.diagonal (eJd J) * Matrix.diagonal (eJd J) = (1 : Matrix (Fin 6) (Fin 6) (ZMod 3)) := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  unfold eJd
  split_ifs <;> decide

@[expose] def eJ (J : Finset (Fin 6)) : GL6 :=
  ⟨Matrix.diagonal (eJd J), Matrix.diagonal (eJd J), eJ_mat_sq J, eJ_mat_sq J⟩


@[expose] def spn (s : Set V6) : Sub6 := Submodule.span (ZMod 3) s


@[expose] def Lambda : Set Sub6 := {S | ∃ i : Fin 6, S = spn {xvec i}}


@[expose] def M2Dot : Subgroup GL6 := MDot ⊓ MulAction.stabilizer GL6 Lambda

@[expose] noncomputable def Q2Dot : Subgroup GL6 :=
  Subgroup.closure {g | ∃ J : Finset (Fin 6), J ⊆ Iset ∧ Even J.card ∧ g = eJ J}


@[expose] def Q8SqK : Subgroup (QuaternionGroup 2 × QuaternionGroup 2) :=
  Subgroup.zpowers (QuaternionGroup.a 2, QuaternionGroup.a 2)

theorem Q8SqK_le_center : Q8SqK ≤ Subgroup.center (QuaternionGroup 2 × QuaternionGroup 2) := by
  rw [Q8SqK, Subgroup.zpowers_le, Subgroup.mem_center_iff]
  rintro ⟨g1, g2⟩
  have h : ∀ g : QuaternionGroup 2, g * QuaternionGroup.a 2 = QuaternionGroup.a 2 * g := by decide
  exact Prod.ext (h g1) (h g2)

instance Q8SqK.normal : Q8SqK.Normal := Subgroup.normal_of_le_center Q8SqK_le_center


theorem qV_smul_of_mem_isometryCore {g : GL6} (hg : g ∈ CFSG.MatrixModel.isometryCore qV) :
    ∀ v : V6, qV (g • v) = qV v := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => intro v; exact hx v
  | one => intro v; simp
  | mul x y _ _ hx hy => intro v; rw [mul_smul, hx, hy]
  | inv x _ hx =>
    intro v
    have := hx (x⁻¹ • v)
    rw [smul_inv_smul] at this
    exact this.symm

theorem commutator_le_self' (H : Subgroup GL6) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem MDot_le_OVq : MDot ≤ OVq := commutator_le_self' _


end

end CFSG.Quasithin.SimsF5
