module

public import CFSG.Quasithin.Background.HMathieuPred
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

@[expose] def xiCandsT (F : List (List Nat)) (m : Nat) (S : List Nat) : List Nat :=
  (S.filter fun s => !(Nat.beq s m)).flatMap fun s => F.getD s []

@[expose] def indepK (r : Nat) (vs b : List Nat) : Bool :=
  decide (r ≤ b.length) && b.all (fun x => vs.contains x) && nodupB (combos b) 0

@[expose] def predXiK (n r fb : Nat) (F : List (List Nat)) (m : Nat) (L S : List Nat)
    (st : List (List Nat) × List Nat) : Bool :=
  L.isEmpty || (decide (L.length ≤ 4) && decide (L.length + 2 ≤ n - Nat.log 2 st.2.length) &&
    (L.length != 4 || (decide (st.2.length ≤ 2 ^ fb) &&
      indepK r (xiCandsT F m S) (pickBasis (xiCandsT F m S)))))

end CFSG.KC.HMathieu

end
