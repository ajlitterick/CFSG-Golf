
module

public import CFSG.GH74.E2.Alpha1Rank
public import CFSG.GH74.E2.Alpha1AutCert
public import CFSG.GH74.E2.NonCentralProd
public import CFSG.GH74.E2.QuasiRank
public import CFSG.GH74.E2.CaseIGlue
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public meta import CFSG.GH74.E2.SD16Cert
public import CFSG.GH74.E2.Alpha1CoreInputs
public meta import CFSG.GH74.E2.Alpha1CoreInputs
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GH74.AS16.Defs
public import CFSG.GH74.E2.Components
public import CFSG.GH74.E2.DtSylow
public import CFSG.GH74.E2.OddRankG
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1

@[expose] public section

namespace CFSG.GH74.E2

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.Semidihedral

section SD16Facts

instance (x : SD16M) : Decidable (IsCentralInv16 x) :=
  inferInstanceAs (Decidable ((∀ w, w * x = x * w) ∧ x * x = 1))

end SD16Facts

end CFSG.GH74.E2
