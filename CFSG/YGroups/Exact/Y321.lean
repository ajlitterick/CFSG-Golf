module

public import CFSG.YGroups.Chain
public import CFSG.YGroups.Exact.Model
public import CFSG.YGroups.Exact.ModelRep
public import CFSG.YGroups.Exact.Y321Inputs
public import Certificates.Certificate10097
public import Certificates.Data.CFSGNative.YGroups.ExactData
public meta import CFSG.YGroups.Defs
public meta import Certificates.Data.CFSGNative.YGroups.Check
public meta import Certificates.Data.CFSGNative.YGroups.ExactCheck
public meta import Certificates.Data.CFSGNative.YGroups.ExactData
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.YGroups

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Certificates.CosetEnumeration (evalWord)


theorem y321 :
    Finite (YGroup 3 2 1) ∧ Nat.card (YGroup 3 2 1) ≤ 2903040 :=
  Certificates.certificate10097.1

theorem y321_check : y321Arrays.size = 7 ∧
    (∀ c < 7, Rep 56 y321Arrays[c]! (arrGen 56 y321Arrays c)) ∧
    (∀ w ∈ yRels 3 2 1, evalWord (arrGen 56 y321Arrays) w = 1) ∧
    2903040 ≤ Nat.card (arrClosure 56 y321Arrays) :=
  Certificates.certificate10097.2

@[expose] noncomputable def y321Gen (c : ℕ) : Equiv.Perm (Fin 56) :=
  arrGen 56 y321Arrays c


theorem y321_relators : ∀ w ∈ yRels 3 2 1, evalWord y321Gen w = 1 :=
  y321_check.2.2.1

noncomputable def y321Model : YGroup 3 2 1 →* Equiv.Perm (Fin 56) :=
  yModelHom y321Gen y321_relators


private theorem y321_model_spec :
    Function.Injective y321Model ∧ Nat.card (YGroup 3 2 1) = 2903040 :=
  yModelHom_injective_and_card_of_le (n := 56) (O := y321Arrays) y321
    (by simp [ngen, y321_check.1]) y321_relators y321_check.2.2.2


theorem card_y321 :
    Nat.card (YGroup 3 2 1) = 2903040 := y321_model_spec.2


end CFSG.YGroups
