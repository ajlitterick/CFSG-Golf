module

public import Certificates.Data.OmegaSevenMax.Tables
public import Certificates.Data.OmegaSevenMax.Defs

public section

namespace Certificates.OmegaSevenMax

structure Tables where
  genU : Array ℕ
  genW : Array ℕ
  treePar : Array ℕ
  treeGen : Array ℕ
  cls : Array ℕ
  clsPar : Array ℕ
  clsGen : Array ℕ
  clsRoot : Array ℕ
  roots : List ℕ

@[expose] def parseNats (s : String) : Array ℕ := ((s.splitOn ",").map String.toNat!).toArray

@[expose] def tables (_ : Unit := ()) : Tables where
  genU := parseNats genUStr
  genW := parseNats genWStr
  treePar := parseNats treeParStr
  treeGen := parseNats treeGenStr
  cls := parseNats clsStr
  clsPar := parseNats clsParStr
  clsGen := parseNats clsGenStr
  clsRoot := parseNats clsRootStr
  roots := rootList


@[expose] def bitsOf (L : List ℕ) : ℕ := L.foldl (fun acc c => acc ||| (1 <<< c)) 0


end Certificates.OmegaSevenMax

end
