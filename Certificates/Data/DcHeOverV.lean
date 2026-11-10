module

public import CFSG.Quasithin.H13.LocDblHeCheckInputs

public section

namespace CFSG.Quasithin.H13.LocDbl.HeCert

open CFSG.Quasithin.H13.LocDbl.DcNative
open CFSG.QuasithinUnique.K1.SporadicPerm (slpTabsA)

@[expose] def hAWordA : List Nat := [0]

@[expose] def hAWordB : List Nat := [1, 4, 2]

@[expose] def hAProg : List (Nat × Nat) :=
  [(0, 0), (0, 2), (1, 3), (0, 4), (0, 5), (1, 6), (0, 7), (1, 8), (1, 9), (1, 10), (1, 11), (0, 12), (1, 13), (1, 14), (1, 15), (1, 16), (0, 17), (1, 18), (1, 19), (0, 1), (1, 21), (1, 22), (0, 23), (0, 24), (1, 25), (0, 26), (0, 27), (1, 28), (0, 29), (1, 30), (0, 31), (0, 32), (0, 33), (1, 34), (1, 35), (1, 36), (1, 37), (0, 38), (1, 39), (1, 0), (1, 41), (1, 42), (1, 43), (0, 44), (0, 45), (1, 46), (0, 47), (0, 48), (1, 49)]

@[expose] def hAQp : List Nat := [0, 20, 40, 50]

@[expose] def hALetters : Array (Array Nat) :=
  heD.VG vData[0]!.1

@[expose] def hATa : Array Nat := tabW 8330 hALetters hAWordA

@[expose] def hATb : Array Nat := tabW 8330 hALetters hAWordB

@[expose] def hAAB : Array (Array Nat) := #[hATa, hATb, invTab hATa, invTab hATb]

@[expose] def hART : Array (Array Nat) :=
  (hAQp.map fun i => (slpTabsA hATa hATb hAProg)[i]!).toArray

@[expose] def hARepsStr : String :=
  "3301,1011,1101,111,1,303011,101,30101,301,330101,11101"

@[expose] def hAEdgesStr : String :=
  "0 2 16630801323831663,2 0 6136192413832412,1 2 212318013238223,2 1 21231801323831413,3 6 \
  132320861368316630,2 3 31360861368314,4 0 600821231863161,2 4 23012923012813201,5 2 \
  241388122310,1 5 24138241382121,6 2 61019132318631310,2 6 23012813231861301,7 2 31360883141,\
  2 7 6136813120183122,8 0 6136182413836601,2 8 230128823201,9 1 241388123120,2 9 82413863616,\
  10 2 21231882310130,2 10 1312019613681361310"

@[expose] def hAInEdgeStr : String :=
  "0 2 0 4 6 8 10 12 14 16 18"

@[expose] def hADInStr : String :=
  "1 1 0 2 2 1 1 1 2 2 1"

@[expose] def hAReachStr : String :=
  "0 1 2 3 4 5 6 7 8 9 10"

@[expose] def hAOutEdgeStr : String :=
  "1 3 0 5 7 9 11 13 15 17 19"

@[expose] def hADOutStr : String :=
  "1 1 0 1 1 2 1 1 1 1 1"

@[expose] def hARoot : Nat := 2

@[expose] def hAVData : List (List (List Nat) × Nat) := [
   ([[1, 1]], 9216),
   ([[3, 3, 0, 3, 0, 1, 0, 1]], 9216)]

@[expose] def hAVs : List (List (List Nat) × Array Nat × Array Nat × Nat) :=
  hAVData.map fun V =>
    let e := bfsEnumL 8330 B (hART ++ (V.1.map (tabW 8330 hAAB)).toArray) (V.2 + 10)
    (V.1, e.1, e.2, V.2)

@[expose] def heDcA : DcData where
  n := 8330
  B := B
  AB := hAAB
  RT := hART
  RTi := hART.map invTab
  NR := 1024
  rpar := (bfsEnumL 8330 B hART 1100).1
  rlab := (bfsEnumL 8330 B hART 1100).2
  lb := orbitLabels 8330 hART
  reps := parseWords hARepsStr
  edges := parseEdges hAEdgesStr
  c0 := hARoot
  inEdge := parseNats hAInEdgeStr
  dIn := parseNats hADInStr
  reach := (parseNats hAReachStr).toList
  outEdge := parseNats hAOutEdgeStr
  dOut := parseNats hADOutStr
  Vs := hAVs
  order := 138240


@[expose] def hBWordB : List Nat := [4]


@[expose] def hBLetters : Array (Array Nat) :=
  heD.VG vData[1]!.1


@[expose] def hBTb : Array Nat := tabW 8330 hBLetters hBWordB


end CFSG.Quasithin.H13.LocDbl.HeCert
