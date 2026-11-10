module

public import CFSG.GH74.GLS.Stage4.Q9.ModelBase
public import CFSG.CharacterTheory.PSL2Table
public import CFSG.GH74.GLS.Stage4.Q9.TablesInputs
public import CFSG.Certificates.Kernel.Q9SLSound
public import Certificates.Kernel.Q9SL.Data
import Certificates.Kernel.Q9SL.Checks
import all CFSG.GH74.GLS.Stage4.Q9.ModelBaseInputs
import all CFSG.GH74.GLS.Stage4.Q9.ModelBase
import all CFSG.GH74.GLS.Stage4.Q9.TablesInputs

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelQ9SL

open CFSG.KC.Q9SL CFSG.GH74.GLS.Stage4.Q9 CFSG.GH74.GLS.Stage4.Q9.Tables

local notation "𝕄" => Matrix (Fin 2) (Fin 2) F9


end CertificateChecks.KernelQ9SL
