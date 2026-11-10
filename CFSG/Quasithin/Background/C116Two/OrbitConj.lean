module

public import CFSG.Quasithin.Background.C2Defs
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.Quasithin.C116Two

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]


theorem conjByElt_one (K : Subgroup G) : conjByElt 1 K = K := by
  ext x
  simp [mem_conjByElt]

theorem conjByElt_mul (b a : G) (K : Subgroup G) :
    conjByElt b (conjByElt a K) = conjByElt (b * a) K := by
  ext x
  simp only [mem_conjByElt, mul_inv_rev, mul_assoc]


end CFSG.Quasithin.C116Two
