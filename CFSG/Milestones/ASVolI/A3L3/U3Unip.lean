module

public import CFSG.Milestones.ASVolI.A3L3.U3Facts

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts

variable {p : ℕ} {K : Type} [Field K]


section Model

variable (hU : UnitaryFieldData p 1 K) [Finite K] (two_ne : (2 : K) ≠ 0) {x y cc : K}
  (hdet : cc ^ 2 * (x ^ 2 + y ^ 2) = -1) (hx : hU.bar x = x) (hy : hU.bar y = y)
  (hc : hU.bar cc = -cc)

local notation "MU" => burnsideA315y_u3Model hU two_ne hdet hx hy hc


end Model

end CFSG.ASVolI
