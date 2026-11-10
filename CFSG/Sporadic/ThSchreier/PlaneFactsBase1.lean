
module

public import CFSG.Sporadic.ThSchreier.PlaneFactsBase
import all CFSG.Sporadic.ThSchreier.PlaneFactsBase

public import CFSG.Sporadic.ThSchreier.GlobalIndexBase1
public import Certificates.Certificate2317
public meta import CFSG.Sporadic.ThSchreier.Text
public meta import CFSG.Sporadic.ThSchreier.Row
public meta import CFSG.Sporadic.ThSchreier.LocalOrbitBase1
public meta import Certificates.Data.CFSGNative.Th.Base
public meta import CFSG.Sporadic.ThSchreier.CentralizerData
public meta import CFSG.Sporadic.ThSchreier.WordsBase1
public import CFSG.Sporadic.ThSchreier.CentralizerData

@[expose] public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 Pointwise

open Matrix in
theorem formF_injective : Function.Injective fun v : V => rowsMatrix fcRows *ᵥ v :=
  fun _ _ h => psi_injective (congrArg toRow h)

theorem rowKeyOf_canonical (hF : OrbitFacts) {i : ℕ} (hi : i < nX) :
    (rowKeyOf (readKey thSt.keys i)).isCanonical = true :=
  imageKey_isCanonical fcRows (hF.canonical i hi) formF_injective

theorem centFixed_length : centFixedIdx.length = 10200 := ctuc_Th_centralizer_plane_data.2.2.2.2.2.1

theorem centImage_length : centImageIdx.length = 120 :=
  ctuc_Th_centralizer_plane_data.2.2.2.2.2.2.1

theorem centImageRows_length : centImageRows.length = 240 :=
  ctuc_Th_centralizer_plane_data.2.2.2.2.2.2.2.1

theorem centImageRows_lt : ∀ n ∈ centImageRows, n < 2 ^ 248 :=
  ctuc_Th_centralizer_plane_data.2.2.2.2.2.2.2.2.1

private theorem native_star_mem : 120754 ∈ centImageIdx :=
  Certificates.certificate2317

section Facts

variable (hF : OrbitFacts) (hS : ThScanFacts)
include hF hS

end Facts

end CFSG.Sporadic.ThSchreier
