module

public import Certificates.Data.RudvalisFF81Sp6Transv

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.Quasithin.G2U
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec21.FF81.Sp6Transv

@[expose] def sw01C : List ℕ :=
  [0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0,
    0, 0, 0, 0, 1]

@[expose] def c7Gen0 : List ℕ :=
  [1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1,
    0, 1, 0, 1, 1]

@[expose] def c7Gen0Inv : List ℕ :=
  [1, 1, 0, 0, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1,
    0, 1, 0, 1, 0]

@[expose] def c7Gen1 : List ℕ :=
  [0, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0,
    1, 0, 1, 1, 1]

@[expose] def c7Gen1Inv : List ℕ :=
  [1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1,
    0, 0, 1, 1, 1]

@[expose] def r0Gen0 : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 1, 1, 0,
    1, 1, 0, 0, 0]

@[expose] def r0Gen1 : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 1, 1]

@[expose] def r0Gen2 : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 1, 0, 1, 0]

@[expose] def r2Gen0 : List ℕ :=
  [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 1]

@[expose] def r2Gen1 : List ℕ :=
  [1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 0, 0, 0, 1]

@[expose] def r4Gen0 : List ℕ :=
  [1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 0, 1,
    1, 0, 1, 1, 1]

@[expose] def r4Gen1 : List ℕ :=
  [1, 0, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1,
    1, 0, 0, 0, 1]

@[expose] def nP : List (List ℕ × List ℕ) :=
  [zPair 0, (fl0C, fl0C), (sw01C, sw01C), tPair]


@[expose] def l1C : List (List ℕ) :=
  [(zPair 0).1, (zPair 0).2, (zPair 1).1, (zPair 1).2, (zPair 2).1, (zPair 2).2]

@[expose] def c7P : List (List ℕ × List ℕ) :=
  [(c7Gen0, c7Gen0Inv), (c7Gen1, c7Gen1Inv)]


@[expose] def wtIdx (i : ℕ) : ℕ :=
  (if i / 9 = 0 then 0 else 1) + (if i / 3 % 3 = 0 then 0 else 1) + (if i % 3 = 0 then 0 else 1)


end CFSG.RankThree.PartTwo.Sec21.FF81.Sp6RefS
