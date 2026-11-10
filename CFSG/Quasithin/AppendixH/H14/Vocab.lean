module

public import CFSG.Milestones.ASVolI.H13

public section

open scoped Pointwise Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open CFSG.Monster.Code

@[expose] def conjSubg {X : Type*} [Group X] (g : X) (A : Subgroup X) : Subgroup X :=
  A.map (MulAut.conj g).toMonoidHom


@[expose] def MY {α : Type*} [MulAction S24 α] (Γ : Subgroup S24) (Y : α) : Subgroup S24 :=
  Γ ⊓ MulAction.stabilizer S24 Y


end CFSG.ASVolI.ChH
