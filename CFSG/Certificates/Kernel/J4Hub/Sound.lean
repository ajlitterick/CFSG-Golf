module

public import CFSG.Certificates.Kernel.J4Hub.RegSound
public import CFSG.Certificates.Kernel.J4Hub.PcSound
public import CFSG.Certificates.Kernel.J4Hub.FlagSound
public import CFSG.Certificates.Kernel.J4Hub.FixedSound
public import CFSG.Certificates.Kernel.J4Hub.BfsSound
public import CFSG.Certificates.Kernel.J4Hub.PrimSubSound

public section

namespace CFSG.KS.J4Hub

open CFSG.KC.Ord CFSG.KS.Ord Matrix

variable {p d w S T L H CM RM ONE LV HV nb : Nat}

theorem one_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S) :
    validM p nb L H ONE = true ∧ ordMat p d w S ONE = 1 :=
  one_sound' hc hnb

theorem mul_sound (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {A B : Nat} (hA : validM p nb L H A = true) (hB : validM p nb L H B = true) :
    validM p nb L H (mulR p w S d T L H CM RM A B) = true ∧
      ordMat p d w S (mulR p w S d T L H CM RM A B) = ordMat p d w S A * ordMat p d w S B :=
  mul_sound' hc hnb hA hB

theorem ordMat_inj (hc : constsOK p w S d T L H CM RM ONE LV HV = true) (hnb : nb = d * S)
    {A B : Nat} (hA : validM p nb L H A = true) (hB : validM p nb L H B = true)
    (h : ordMat p d w S A = ordMat p d w S B) : A = B :=
  ordMat_inj' hc hnb hA hB h


end CFSG.KS.J4Hub

end
