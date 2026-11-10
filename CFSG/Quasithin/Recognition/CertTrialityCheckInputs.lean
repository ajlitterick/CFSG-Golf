module

public import CFSG.Quasithin.Recognition.CertChain
public import CFSG.Quasithin.Recognition.CertTrialityModel
public import CFSG.Quasithin.Recognition.CertDataTriality
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public meta import CFSG.Open.QuasithinDefs
public meta import CFSG.Quasithin.Recognition.CertF8
public meta import CFSG.Quasithin.Recognition.CertTrialityModel
public meta import CFSG.Quasithin.Recognition.CertDataTriality
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.Schreier.Check

public section

namespace CFSG.Quasithin

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

instance : Inhabited GF8 := ⟨0⟩


@[expose] def IsNormalized (v : Fin 8 → GF8) : Prop :=
  ∃ t : Fin 8, v t = 1 ∧ ∀ s : Fin 8, s < t → v s = 0

instance (v : Fin 8 → GF8) : Decidable (IsNormalized v) :=
  inferInstanceAs (Decidable (∃ t : Fin 8, v t = 1 ∧ ∀ s : Fin 8, s < t → v s = 0))


end CFSG.Quasithin
