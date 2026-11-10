module

public import CFSG.GH74.Generic.ComponentShapes
public import CFSG.GH74.Generic.OuterInvolution
public import CFSG.GH74.Generic.QuaternionCentral

public section

namespace CFSG.GH74.Generic

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.Assembly.LowTwoRank CFSG.Blueprint Subgroup
  CFSG.GH74.Filter.ClassicalOdd

variable {G : Type} [Group G]

theorem ShapeS1.q8Frame {x : G} {K : Subgroup (CentralizerBar x)} (h : ShapeS1 x K) :
    Q8Frame ↥K :=
  IsSL4Model.q8Frame h.1

theorem ShapeS2.q8Frame {x : G} {K : Subgroup (CentralizerBar x)} (h : ShapeS2 x K) :
    Q8Frame ↥K := by
  obtain ⟨⟨F, _, _, hodd, ⟨e⟩⟩, -⟩ := h
  have hF2 : ringChar F ≠ 2 := ringChar_ne_two_of_two_ne_zero (two_ne_zero_of_odd_card hodd)
  obtain ⟨φ, hφ, w, hww, hsw⟩ := exists_q8q8_Sp4 hF2
  exact Q8Frame.of_mulEquiv ⟨φ, hφ, w, hww, hsw⟩ e.symm


@[expose] def twistedFixed {K : Type} [Group K] (α : MulAut K) (k : K) : Subgroup K :=
  MonoidHom.eqLocus (MulAut.conj k * α).toMonoidHom (MonoidHom.id K)


end CFSG.GH74.Generic
