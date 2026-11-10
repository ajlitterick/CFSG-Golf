module

public import Mathlib
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.Subgroup.Center
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.RingTheory.TensorProduct.Finite
public import CFSG.Open.OrderForm
public import CFSG.Assembly.OrderReductions.Helpers
public import CFSG.Assembly.OrderReductions.InvolutionGraph
public import CFSG.Assembly.OrderReductions.PermutationReduction
public import CFSG.Assembly.OrderReductions.StrongEmbedding

public section

open CFSG.Open

namespace CFSG.OrderReductions.Reduction


theorem proper_subgroup_card_lt (group : Type*) [Group group] [Finite group]
    (subgroup : Subgroup group) (proper : subgroup ≠ ⊤) :
    Nat.card subgroup < Nat.card group := by
  apply Nat.lt_of_le_of_ne (subgroup.card_le_card_group)
  intro equal_card
  exact proper (subgroup.eq_top_of_card_eq equal_card)


end CFSG.OrderReductions.Reduction
