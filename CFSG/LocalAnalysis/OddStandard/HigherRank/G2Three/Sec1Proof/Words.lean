module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.ModelDef

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec1Proof

open CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.RankThree.PartTwo.Census.Carrier.G2Three

@[expose] def gx0P (_ : Unit := ()) : List ℕ := mkPc false x0c x1c

@[expose] def gx1P (_ : Unit := ()) : List ℕ := mkPc false x1c x0c

@[expose] def gy0P (_ : Unit := ()) : List ℕ := mkPc false y0c y1c

@[expose] def gy1P (_ : Unit := ()) : List ℕ := mkPc false y1c y0c

@[expose] def gsP (_ : Unit := ()) : List ℕ := mkPc true one14 one14


variable {G : Type} [Group G] [Finite G]

private theorem length_x0c : x0c.length = 196 := by decide +kernel

private theorem length_x1c : x1c.length = 196 := by decide +kernel

private theorem length_y0c : y0c.length = 196 := by decide +kernel

private theorem length_y1c : y1c.length = 196 := by decide +kernel

theorem decPc_gx0P : decPc (gx0P ()) = gx0W := by
  show decPc (mkPc false x0c x1c) = wdiag (dec14 x0c) (dec14 x1c)
  rw [decPc_mkPc_false length_x0c length_x1c]

theorem decPc_gx1P : decPc (gx1P ()) = gx1W := by
  show decPc (mkPc false x1c x0c) = wdiag (dec14 x1c) (dec14 x0c)
  rw [decPc_mkPc_false length_x1c length_x0c]

theorem decPc_gy0P : decPc (gy0P ()) = gy0W := by
  show decPc (mkPc false y0c y1c) = wdiag (dec14 y0c) (dec14 y1c)
  rw [decPc_mkPc_false length_y0c length_y1c]

theorem decPc_gy1P : decPc (gy1P ()) = gy1W := by
  show decPc (mkPc false y1c y0c) = wdiag (dec14 y1c) (dec14 y0c)
  rw [decPc_mkPc_false length_y1c length_y0c]

theorem decPc_gsP : decPc (gsP ()) = gsW := by
  show decPc (mkPc true one14 one14) = wanti 1 1
  rw [decPc_mkPc_true length_one14 length_one14, dec14_one14]


end CFSG.OddStandard.HigherRank.G2Three.Sec1Proof
