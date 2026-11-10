module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.PowerMap

public section

namespace CFSG.GroupTheory

open Subgroup

variable {A : Type*} [Group A]


@[expose]
noncomputable def MulAut.restrictNormal (α : MulAut A) (N : Subgroup A)
    (hN : N.map α.toMonoidHom = N) : MulAut N :=
  (α.subgroupMap N).trans (MulEquiv.subgroupCongr hN)

@[simp]
theorem MulAut.restrictNormal_apply (α : MulAut A) (N : Subgroup A)
    (hN : N.map α.toMonoidHom = N) (n : N) :
    ((MulAut.restrictNormal α N hN n : N) : A) = α n := rfl

@[expose]
noncomputable def MulAut.quotientNormal (α : MulAut A) (N : Subgroup A) [N.Normal]
    (hN : N.map α.toMonoidHom = N) : MulAut (A ⧸ N) :=
  QuotientGroup.congr N N α hN

@[simp]
theorem MulAut.quotientNormal_mk (α : MulAut A) (N : Subgroup A) [N.Normal]
    (hN : N.map α.toMonoidHom = N) (a : A) :
    MulAut.quotientNormal α N hN (a : A ⧸ N) = (α a : A ⧸ N) :=
  QuotientGroup.congr_mk N N α hN a


end CFSG.GroupTheory

end
