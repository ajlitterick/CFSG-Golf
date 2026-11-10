module

public import Certificates.Data.Item434SmallTwoIII

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII

@[expose] def s0C : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 1]

@[expose] def fl0C : List ℕ :=
  [0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1]

@[expose] def fl2C : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0,
    1, 0, 0, 0]

@[expose] def csG0 : List ℕ :=
  [1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 0, 1,
    1, 1, 1, 0]

@[expose] def csG0I : List ℕ :=
  [0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0,
    1, 0, 0, 0]

@[expose] def csG1 : List ℕ :=
  [0, 1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0,
    0, 0, 0, 0]

@[expose] def csG1I : List ℕ :=
  [0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1,
    0, 0, 1, 0]

@[expose] def qG0 : List ℕ :=
  [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 0,
    0, 0, 0, 1]

@[expose] def qG1 : List ℕ :=
  [1, 1, 0, 0, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1,
    0, 0, 1, 1]

@[expose] def qG2 : List ℕ :=
  [1, 1, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0,
    0, 0, 0, 1]

@[expose] def qG3 : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1,
    0, 0, 1, 1]

@[expose] def qG4 : List ℕ :=
  [1, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 1]


@[expose] def inv6 (x : List ℕ) : List ℕ :=
  mul6 (mul6 j6C (tr6 x)) j6C

@[expose] def conj6 (c x : List ℕ) : List ℕ :=
  mul6 (mul6 c x) (inv6 c)


end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv
