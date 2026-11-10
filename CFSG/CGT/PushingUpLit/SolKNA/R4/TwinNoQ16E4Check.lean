module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporE81Check

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.Check

open CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native
open CFSG.RankThree.PartTwo.Sec4.Item434SporE81 (posWord)

structure Q16Data where
  n : ℕ
  pg : Array (Array ℕ)
  qW : Array (List ℕ)
  qKeys : List ℕ
  qFuel : ℕ
  qOrd : ℕ

@[expose] def qGens (X : Q16Data) : Array (Array ℕ) := X.qW.map (posWord X.n X.pg)

@[expose] def qCert (X : Q16Data) : ArrCert := enumBfs X.n (qGens X) X.qKeys X.qFuel


end CFSG.CGT.PushingUpLit.SolKNA.R4.Check
