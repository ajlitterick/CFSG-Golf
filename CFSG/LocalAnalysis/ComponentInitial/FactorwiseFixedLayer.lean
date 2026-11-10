module

public import CFSG.LocalAnalysis.ComponentInitial.FixedComponentCorrespondence

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped commutatorElement

variable {M : Type*} [Group M] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem commute_of_commutator_eq_bot {H K : Subgroup M} (h : ⁅H, K⁆ = ⊥) {x y : M} (hx : x ∈ H)
    (hy : y ∈ K) : x * y = y * x := by
  have := Subgroup.commutator_mem_commutator hx hy
  rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
  exact this


@[expose] def restrictAut (a : MulAut M) (H : Subgroup M) (hH : H.map a.toMonoidHom = H) :
    MulAut H :=
  (MulEquiv.subgroupMap a H).trans (MulEquiv.subgroupCongr hH)

theorem coe_restrictAut (a : MulAut M) (H : Subgroup M) (hH : H.map a.toMonoidHom = H) (x : H) :
    ((restrictAut a H hH x : H) : M) = a x := rfl

@[expose] def coordAut (a : MulAut M) (A : ι → Subgroup M)
    (hA : ∀ i, (A i).map a.toMonoidHom = A i) : MulAut (∀ i, A i) :=
  MulEquiv.piCongrRight fun i => restrictAut a (A i) (hA i)

section


end

section Fixed


end Fixed


end CFSG.LocalAnalysis.ComponentInitial
