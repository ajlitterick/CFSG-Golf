module  -- shake: keep-all --deprecated_module: ignore

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Clifford
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ElementaryAbelianAction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ExtraspecialFixedPoints
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.FreeBasis
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.InducedIrreducible
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.kerRepresentation
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.PermutationBasisOrbits
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.ScalarDescent
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.TwoDimensionalOddOrder

namespace CFSG
end CFSG
open CFSG

/-!
# Representation theory infrastructure

Generic representation theory of groups over `ℂ` (and other fields): Maschke
and complete reducibility, subrepresentation lattices, representation
equivalences, induction and coinduction, Jacobson density, and the
extraspecial and solvable group representation machinery.  Character theory
built on top of this lives in `Theory/Character`.
-/
