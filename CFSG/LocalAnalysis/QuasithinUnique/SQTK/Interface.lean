module

public import CFSG.Open.SQTKSimpleListTauCeti

public section

namespace CFSG.QuasithinUnique.SQTK

open CFSG.Assembly CFSG.Open.SQTKTauCeti

@[expose] def IsSQTKSporadicName (s : TauCeti.SporadicName) : Prop :=
  s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
    s = .J1 ∨ s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru

instance (s : TauCeti.SporadicName) : Decidable (IsSQTKSporadicName s) := by
  unfold IsSQTKSporadicName; infer_instance


end CFSG.QuasithinUnique.SQTK
