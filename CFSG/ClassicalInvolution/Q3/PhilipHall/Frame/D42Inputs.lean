module

public import CFSG.ClassicalInvolution.Q3.Q3TLTO8Inputs
public import CFSG.Sporadic.SmallOddCore.LocalCheck
public import Certificates.Data.PhilipHallD42

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42

open CFSG.EvenSmallLie.OmegaEight CFSG.Certificates.Native CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore.Native
  CFSG.Sporadic.SmallOddCore CFSG.ComponentClassification.J2Cover CFSG.ClassicalInvolution.Q3.O8
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42Data CFSG.ClassicalInvolution.O8Data


@[expose] def mainIdx (j : ℕ) : ℕ := if j = 0 then 0 else 2

@[expose] def zTbl (j : ℕ) : Table := arrTable 360 (mainArrs.getD (mainIdx j) #[])

@[expose] def pGens (j : ℕ) : List Table := (pWords.getD j []).map fun w => arrTable 360 (autW w)

@[expose] def cgTbls (j : ℕ) : List Table :=
  let T := (centGens.getD (mainIdx j) []).map fun w => arrTable 360 (omegaW w)
  T ++ T.map (invT 360)

@[expose] def uGens (j : ℕ) : List Table := (uWords.getD j []).map (wordTbl 360 (cgTbls j))

@[expose] def omegaLevels : Array Level := rawLevels 360 omegaS (omegaBase.map Fin.val).toArray

@[expose] def siftOmega (lv : Array Level) (T : Table) : Bool :=
  siftA 360 lv (omegaBase.map Fin.val).toArray 0 (natArr T)

@[expose] def pOrder (j : ℕ) : ℕ := if j = 0 then 81 else 9

@[expose] def sylowCheck (j : ℕ) : Bool :=
  (pWords.getD j []).all (fun w => lettersOK 18 w) &&
    (pGens j).all (fun g => permOK 360 g && invOK 360 g (invT 360 g) && commTT 360 g (zTbl j)) &&
    enumOK 360 (pOrder j) (pOrder j) (pGens j)

@[expose] def uCheck (j : ℕ) : Bool :=
  let lv := omegaLevels
  (uGens j).all (fun g => permOK 360 g && siftOmega lv g && commTT 360 g (zTbl j)) &&
    enumOK 360 512 512 (uGens j) && normOK 360 512 (uGens j) (pGens j)


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.D42
