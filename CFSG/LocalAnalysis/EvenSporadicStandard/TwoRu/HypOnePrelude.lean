
module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoRu.HypOneBaseRu
public import Certificates.Certificate24370
public import Certificates.Certificate24371
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Generic

@[expose] public section

namespace CFSG.EvenSporadicStandard.TwoRu.HypOne

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Schreier
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 CFSG.Sporadic.RuSchreier
open CFSG.ComponentClassification.M12Cover CFSG.EvenSporadicStandard.HypOne
open CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Th (Rep)


theorem getElem!_map_tblOfArr {A : Array (Array ℕ)} {l : ℕ} (hl : l < A.size) :
    (A.map tblOfArr)[l]! = tblOfArr A[l]! := by
  rw [getElem!_pos (A.map tblOfArr) l (by simpa using hl), getElem!_pos A l hl, Array.getElem_map]

theorem fourClassesLarge_ruC :
    FourClassesLarge ruC :=
  fourClassesLarge_ruC_of_base Certificates.certificate24370

theorem fourClassesLarge_ruL :
    FourClassesLarge ruL :=
  fourClassesLarge_ruL_of_base Certificates.certificate24371

end CFSG.EvenSporadicStandard.TwoRu.HypOne
