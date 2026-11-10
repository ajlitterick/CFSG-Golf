module

public import CFSG.GH74.E2.CaseIINoComp
public import CFSG.RankThree.PartOne.S12.SectionalRank

public section

namespace CFSG.GH74.QTGen4

variable {X : Type*} [Group X]

noncomputable def conjHom (Q : Subgroup X) [Q.Normal] : X →* MulAut Q :=
  Q.normalizerMonoidHom.comp
    (MonoidHom.codRestrict (MonoidHom.id X) (Subgroup.normalizer (Q : Set X))
      fun x => by
        rw [Subgroup.normalizer_eq_top]
        exact Subgroup.mem_top x)


end CFSG.GH74.QTGen4
