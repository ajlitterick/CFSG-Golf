module

public meta import CFSG.Sporadic.Schreier.RuArrays
public import Certificates.Certificate2247

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem ruBasic_check :
    isInvA 4060 ruA0A (ruInv ruA0A) = true ∧ isInvA 4060 ruA1A (ruInv ruA1A) = true ∧
    ruCRunA.2.2 = true ∧ ruNRunA.2.2 = true ∧
    isInvA 4060 ruN0A (ruInv ruN0A) = true ∧ isInvA 4060 ruN1A (ruInv ruN1A) = true ∧
    isInvA 4060 ruC0A (ruInv ruC0A) = true ∧ isInvA 4060 ruC1A (ruInv ruC1A) = true ∧
    isInvA 4060 ruWA (ruInv ruWA) = true ∧ isInvA 4060 ruHA (ruInv ruHA) = true ∧
    isInvA 4060 ruNs0A (ruInv ruNs0A) = true ∧ isInvA 4060 ruNs1A (ruInv ruNs1A) = true ∧
    (∀ i < 4, isInvA 4060 ruSGensA[i]! (ruInv ruSGensA[i]!) = true) ∧
    ruWordsLettersOK = true :=
  Certificates.certificate2247.1


end CFSG.Sporadic.RuSchreier
