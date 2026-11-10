module

public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.AbelianGroup
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.CentralKernel
public import CFSG.ThirdParty.BrauerInduction.Background.LinearChar.Mackey
public import CFSG.ThirdParty.BrauerInduction.Background.LinearChar.OneDimensional
public import CFSG.ThirdParty.BrauerInduction.Background.LinearChar.QuotientDescent
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Nilpotent
public import CFSG.ThirdParty.BrauerInduction.Background.Fintype.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Clifford theory for nilpotent groups

This file formalizes the Clifford-theoretic monomiality theorem for finite
nilpotent groups. In the present development, it is the key ingredient in the
proof of `BrauerSpanChar.le_BrauerSpanLin`: since Brauer-elementary groups are
nilpotent, their irreducible characters are induced from linear characters of
subgroups.

The same argument supplies the monomiality step in Serre's proof of Brauer
induction; see Serre [1977, §10.5, Theorems 19–20], especially the appeal after
Theorem 20 to §8.5, Theorem 16.

The main ingredients are:

* a simple representation restricts nontrivially to a linear character on a
  normal abelian subgroup;
* the associated inertia subgroup induces back to the original representation;
* if the central kernel is trivial, this inertia subgroup is proper;
* if the central kernel is nontrivial, the representation descends to a smaller
  quotient.

Combining these cases proves that every simple representation of a finite
nilpotent group over an algebraically closed field of characteristic zero is
induced from a linear character of a subgroup.
-/

universe u v


open CategoryTheory

namespace FDRep


end FDRep

namespace CFSG.LinearChar


end CFSG.LinearChar

namespace FDRep


end FDRep
