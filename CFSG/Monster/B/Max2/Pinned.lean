module

public import CFSG.Monster.B.Intertwiner.ArithSpec
public import Certificates.Certificate3108
public import Certificates.Data.CFSGNative.MonsterB.Max2Pinned
public import CFSG.Sporadic.HS.SmallF2Spec

public section

namespace CFSG.Monster.B

open Bin Matrix


@[expose] noncomputable def Tmat : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := Dyadic.TK

noncomputable abbrev cMat : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := progRegs genA₁ genA₂ 1

noncomputable abbrev dMat : Matrix (Fin 4370) (Fin 4370) (ZMod 2) := progRegs genA₁ genA₂ 2

theorem pinned_facts :
    cMat * cMat = 1 ∧ cMat ≠ 1 ∧ dMat ^ 48 = 1 ∧ dMat ^ 24 ≠ 1 ∧ dMat ^ 16 ≠ 1 ∧
    dMat ^ 24 * cMat = cMat * dMat ^ 24 ∧ IsUnit Tmat ∧ genA₂ * genA₂ * genA₂ = 1 ∧
    (dMat ^ 24 * (genA₂ * genA₂ * dMat ^ 24 * genA₂)) ^ 5 = 1 :=
  Certificates.certificate3108

end CFSG.Monster.B

end
