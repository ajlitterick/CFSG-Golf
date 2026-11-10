module

public import CFSG.Quasithin.Background.HModChk
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk

@[expose] noncomputable def imgOK (M J : List Nat) : Bool :=
  nodupB (combos (J.map fun j => actM M (2 ^ j) ^^^ 2 ^ j)) 0

@[expose] noncomputable def kerOK (M K : List Nat) : Bool :=
  K.all (fun v => actM M v == v) && nodupB (combos K) 0

@[expose] noncomputable def allImg (n r : Nat) : List (List Nat) → List (List Nat) → Bool
  | [], [] => true
  | M :: Ms, J :: Js =>
    J.length == r && J.all (fun j => decide (j < n)) && imgOK M J && allImg n r Ms Js
  | _, _ => false

@[expose] noncomputable def allKer (n k : Nat) : List (List Nat) → List (List Nat) → Bool
  | [], [] => true
  | M :: Ms, K :: Ks =>
    K.length == k && K.all (fun v => decide (v < 2 ^ n)) && kerOK M K && allKer n k Ms Ks
  | _, _ => false

end CFSG.KC.HMathieu

end
