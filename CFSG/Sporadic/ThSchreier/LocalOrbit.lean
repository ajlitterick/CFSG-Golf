
module

public import CFSG.Sporadic.ThSchreier.LocalOrbitBase1

public import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Sporadic.ThSchreier.Words
public meta import CFSG.Sporadic.ThSchreier.Words
public meta import CFSG.Sporadic.ThSchreier.LocalData
public import CFSG.Sporadic.ThSchreier.LocalOrbitInputs
public import Certificates.Certificate2313
public import Mathlib
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Certificates.SchreierStabilizerGenerators
public import Certificates.Data.CFSGNative.Th.Certificate
public import CFSG.Sporadic.Th.Max3.Data
public meta import CFSG.Sporadic.Th.Chain
public import CFSG.Sporadic.Th.Chain
public meta import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.Sporadic.ThSchreier.AutCore
public meta import Certificates.Certificate10088Base
public import Certificates.Certificate10088Base
public import Certificates.Certificate10089Base
public meta import Certificates.Certificate10089Base
public import Certificates.Certificate10091Base
public meta import Certificates.Certificate10091Base

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

theorem isRows_localX : IsRows rowsLX localX := by
  rw [localX_eq]
  exact isRows_abRows xWord

theorem isRows_localY : IsRows rowsLY localY := by
  rw [localY_eq]
  exact isRows_abRows yWord


private theorem native_matrix_facts :
    eqRows (mulRows rowsLX rowsLX) idRows = true ∧ eqRows rowsLX idRows = false ∧
    eqRows (mulRows (mulRows rowsLY rowsLY) rowsLY) idRows = true ∧
    eqRows rowsLY idRows = false ∧
    eqRows (powRows (mulRows rowsLX rowsLY) 21) idRows = true ∧
    eqRows (powRows (mulRows rowsLX rowsLY) 3) idRows = false ∧
    eqRows (powRows (mulRows rowsLX rowsLY) 7) idRows = false ∧
    imageKey (frTable rowsLX) wKeyRow = wKeyRow ∧
    imageKey (frTable (mulRows rowsLY rowsLY)) wKeyRow = wKeyRow :=
  Certificates.certificate2313.2.2

theorem localX_mul_self : localX * localX = 1 :=
  eq_one_of_isRows (isRows_localX.mul isRows_localX) native_matrix_facts.1

theorem localY_cube : localY * localY * localY = 1 :=
  eq_one_of_isRows ((isRows_localY.mul isRows_localY).mul isRows_localY)
    native_matrix_facts.2.2.1


theorem isRows_localX_inv : IsRows rowsLX localX⁻¹ :=
  isRows_inv_of_mul_self isRows_localX localX_mul_self

theorem isRows_localY_inv : IsRows (mulRows rowsLY rowsLY) localY⁻¹ :=
  isRows_inv_of_cube isRows_localY localY_cube


end CFSG.Sporadic.ThSchreier
