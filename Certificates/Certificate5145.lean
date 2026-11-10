module

public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public import CFSG.GH74.E2.SDExtCertDataInputs
import CFSG.Certificates.Kernel.SD16Ext
meta import CFSG.Certificates.Kernel.Common.Harness
meta import CFSG.Certificates.Kernel.Common.Each

public section

open CFSG
open CFSG.GH74
open CFSG.GH74.E2
open CFSG.GH74.E2.SDW
open CFSG.Semidihedral
attribute [local instance] CFSG.GH74.E2.SDW.instDecEqSD16MForCert

open CFSG.KS.SD16Code

end

