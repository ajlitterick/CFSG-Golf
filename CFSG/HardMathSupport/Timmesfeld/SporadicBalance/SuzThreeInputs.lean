module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThreeKit
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporSuzE81Data
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzThreeKit
public meta import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporSuzE81Data
public meta import CFSG.Monster.B.Mathieu.SylowCore
public meta import Certificates.Data.CFSGNative.Co3Schreier.Basic
public meta import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co3ThreeKit
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Core
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public meta import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public meta import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public meta import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public meta import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
public meta import CFSG.LocalAnalysis.GLTheoremB.QuotientTools

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.RankThree.Native
  CFSG.RankThree.PartOne CFSG.Monster.B.Fischer CFSG.Monster.B.Mathieu CFSG.Sporadic.SuzOddCore
  CFSG.RankThree.PartTwo.Sec4.Item434SporE81 CFSG.Sporadic.Schreier.Co3.Native

@[expose] def hypTuples : Array (Array Nat) :=
  #[#[0, 205, 535, 388, 165, 93], #[0, 343, 916, 1779, 1047, 1303],
    #[3, 730, 473, 1020, 1009, 1186], #[0, 606, 909, 1427, 1449, 364],
    #[11, 1425, 864, 130, 1164, 506], #[0, 1075, 1573, 1202, 62, 1286],
    #[0, 1260, 1642, 253, 1373, 280], #[3, 1227, 580, 1156, 1256, 1226],
    #[11, 1066, 178, 410, 932, 667], #[1, 1688, 1639, 165, 1578, 1186],
    #[1, 1283, 1257, 230, 87, 776], #[5, 696, 1611, 308, 1025, 768],
    #[4, 1736, 764, 547, 1675, 1019], #[11, 594, 831, 451, 1393, 1111],
    #[16, 1734, 364, 1508, 426, 530], #[39, 1430, 20, 570, 1706, 179],
    #[0, 205, 810, 1195, 881, 1707], #[12, 1504, 598, 979, 47, 683],
    #[19, 1337, 233, 328, 143, 1684], #[1, 764, 541, 581, 211, 660],
    #[0, 463, 366, 331, 1258, 1102], #[12, 98, 163, 782, 1607, 783], #[0, 393, 274, 725, 282, 1692],
    #[0, 568, 736, 1760, 604, 951], #[9, 1210, 104, 173, 1058, 845],
    #[3, 870, 1252, 1071, 548, 1595], #[11, 157, 1423, 1666, 777, 994],
    #[5, 1310, 1152, 713, 337, 373], #[1, 1525, 408, 751, 861, 1509], #[1, 1525, 436, 692, 861, 10],
    #[11, 932, 383, 939, 1066, 1525], #[0, 274, 393, 1546, 267, 1700],
    #[2, 179, 89, 1466, 587, 685], #[5, 1463, 1046, 566, 1677, 733],
    #[0, 1409, 171, 1523, 1730, 238], #[6, 167, 91, 1766, 1447, 533],
    #[61, 94, 423, 1685, 1567, 998], #[0, 568, 326, 1694, 736, 511],
    #[0, 1551, 1550, 791, 1258, 132], #[19, 474, 287, 374, 1167, 1516],
    #[5, 1255, 1259, 1571, 175, 214], #[6, 874, 1643, 50, 616, 1286],
    #[6, 1447, 653, 1684, 167, 935], #[11, 1109, 927, 252, 455, 419],
    #[13, 1572, 302, 1764, 108, 844], #[12, 1519, 385, 838, 182, 865],
    #[3, 1279, 279, 1775, 47, 614], #[2, 848, 514, 469, 1172, 1724],
    #[2, 648, 1039, 1781, 1091, 233], #[2, 555, 454, 1240, 1679, 92],
    #[2, 1180, 1163, 789, 275, 1583], #[13, 793, 706, 967, 461, 853],
    #[11, 708, 1135, 266, 1714, 222], #[3, 1120, 1209, 1762, 82, 784],
    #[4, 1079, 1122, 914, 1305, 1699], #[5, 1596, 616, 1450, 1051, 96],
    #[6, 1447, 696, 857, 167, 294], #[9, 257, 135, 1297, 754, 762], #[16, 204, 20, 467, 756, 686],
    #[4, 1473, 1695, 218, 512, 786], #[3, 960, 745, 986, 1426, 815],
    #[30, 1628, 534, 1339, 419, 891], #[2, 837, 955, 1038, 1489, 1126],
    #[90, 1723, 225, 1752, 1772, 257], #[4, 1587, 1608, 1411, 1621, 222],
    #[3, 710, 730, 1537, 155, 731], #[9, 500, 286, 284, 345, 2], #[2, 367, 688, 614, 232, 787],
    #[2, 555, 454, 1722, 1679, 32], #[61, 272, 1545, 646, 1242, 1447],
    #[44, 693, 1436, 1706, 216, 573], #[9, 397, 23, 859, 449, 1405], #[3, 633, 352, 151, 473, 421],
    #[3, 870, 548, 196, 571, 852], #[61, 1242, 1143, 669, 272, 284],
    #[5, 1051, 1596, 566, 1015, 544], #[3, 854, 112, 223, 965, 1356],
    #[9, 1210, 1684, 1497, 1696, 642], #[4, 169, 931, 303, 1725, 1781],
    #[14, 444, 727, 1585, 738, 1127], #[21, 190, 116, 541, 897, 179], #[2, 179, 587, 75, 1172, 725],
    #[6, 1758, 1181, 973, 156, 70], #[44, 1451, 941, 1736, 1190, 1069],
    #[16, 204, 1455, 999, 20, 805], #[5, 278, 122, 1435, 1585, 1194],
    #[13, 1572, 538, 654, 131, 682], #[44, 1053, 1587, 869, 1520, 970],
    #[12, 1504, 431, 1406, 1753, 1721], #[6, 672, 1330, 1257, 448, 344],
    #[6, 1357, 910, 1124, 1249, 570], #[2, 1453, 1663, 436, 1276, 1470],
    #[44, 1520, 1277, 425, 1053, 260], #[2, 837, 1489, 1613, 826, 1035],
    #[9, 1210, 91, 1311, 1684, 150], #[3, 1488, 1412, 1500, 838, 1554],
    #[6, 167, 1447, 1043, 203, 1613], #[11, 927, 505, 1579, 1109, 818],
    #[2, 1054, 1281, 808, 207, 1349], #[5, 372, 226, 1073, 696, 1235],
    #[3, 960, 1426, 1500, 542, 938], #[11, 1757, 1410, 1494, 1400, 1766],
    #[4, 310, 234, 1242, 1003, 963], #[14, 337, 1077, 189, 1208, 1346],
    #[5, 738, 872, 412, 1611, 974], #[5, 1431, 1317, 991, 227, 820], #[9, 32, 577, 225, 612, 936],
    #[3, 47, 1279, 1541, 40, 847], #[13, 793, 1032, 1103, 461, 1107],
    #[39, 418, 802, 1622, 1059, 1160], #[2, 207, 222, 852, 1679, 742],
    #[2, 367, 316, 436, 232, 1031], #[4, 1695, 284, 671, 1473, 739],
    #[2, 207, 1054, 1132, 1726, 1068], #[39, 142, 523, 140, 796, 440],
    #[19, 836, 551, 1559, 233, 22], #[4, 892, 443, 110, 1725, 236], #[6, 805, 29, 1179, 867, 84],
    #[5, 1310, 1463, 406, 1237, 563], #[3, 548, 870, 753, 926, 1741],
    #[4, 1736, 1675, 977, 371, 588]]


@[expose] def yTuple : Array Nat := #[1, 2, 0, 142, 3, 667]

@[expose] def cTuples : Array (Array Nat) :=
  #[#[320, 1758, 1292, 1217, 272, 1588], #[1676, 968, 605, 1271, 273, 462]]


@[expose] def cKeys : List Nat := [0, 1, 2, 3]

@[expose] def levels (_ : Unit := ()) : Array Level :=
  rawLevels 1782 smallStrongArrs smallBaseNat.toArray

@[expose] def inP (L : Array Level) (g : Array Nat) : Bool :=
  siftA 1782 L smallBaseNat.toArray 0 g

@[expose] def qGensS (_ : Unit := ()) : Array (Array Nat) := qGens suzE81


@[expose] def dGens (_ : Unit := ()) : Array (Array Nat) :=
  (suzE81.dW[0]!).map (posWord 1782 (qGensS ()))

@[expose] def digit3 (k i : Nat) : Nat := k / 3 ^ i % 3

@[expose] def dProd (dg : Array (Array Nat)) (k : Nat) : Array Nat :=
  compA 1782 (powArr 1782 dg[0]! (digit3 k 0)) (compA 1782 (powArr 1782 dg[1]! (digit3 k 1))
    (compA 1782 (powArr 1782 dg[2]! (digit3 k 2)) (compA 1782 (powArr 1782 dg[3]! (digit3 k 3))
      (powArr 1782 dg[4]! (digit3 k 4)))))

@[expose] def dElts (_ : Unit := ()) : Array (Array Nat) :=
  Array.ofFn (n := 243) fun k => dProd (dGens ()) k.val


@[expose] def rebuild (L : Array Level) (beta : Array Nat) : Array Nat := Id.run do
  let mut acc := idA 1782
  let mut accI := idA 1782
  for i in [0:6] do
    let k := L[i]!.pos[accI[beta[i]!]!]!
    acc := compA 1782 acc L[i]!.tr[k]!
    accI := compA 1782 L[i]!.trInv[k]! accI
  return acc

@[expose] def inD (E : Array (Array Nat)) (t : Array Nat) : Bool :=
  anyLt 243 fun k => eqA 1782 t E[k]!

@[expose] def yArr (L : Array Level) : Array Nat := rebuild L yTuple

@[expose] def cGens (L : Array Level) : Array (Array Nat) :=
  #[yArr L, rebuild L cTuples[0]!, rebuild L cTuples[1]!]

@[expose] def cCert (L : Array Level) : ArrCert := enumBfs 1782 (cGens L) cKeys 3300


@[expose] def hypG (L : Array Level) : Array (Array Nat) := hypTuples.map (rebuild L)


@[expose] def relsOf (src : Array Nat) (ys : Array (Array Nat)) :
    Array (Option (Nat × Array Nat)) :=
  Array.ofFn (n := 6) fun l => if src[l.val]! < l.val then some (src[l.val]!, ys[l.val]!) else none

@[expose] def fltOf (src : Array Nat) (ys : Array (Array Nat)) : Array (Option (Array Nat)) :=
  Array.ofFn (n := 6) fun l => if src[l.val]! < l.val then none else some ys[l.val]!

@[expose] def predOf (ys : Array (Array Nat)) (a : Array Nat) : Bool :=
  allLt 4 fun t => commA 1782 a ys[t + 6]!

@[expose] def hleaves (L : Array Level) (src : Array Nat) (ys : Array (Array Nat)) :
    List (Array Nat) :=
  SuzT.fsearch 1782 L smallBaseNat.toArray (relsOf src ys) (fltOf src ys) (predOf ys) 6 0
    (idA 1782) (idA 1782)


@[expose] def dCheck (_ : Unit := ()) : Bool :=
  let L := levels ()
  let dg := dGens ()
  let E := dElts ()
  dg.size == 5 &&
  allLt 5 (fun i => validA 1782 dg[i]! && inP L dg[i]! &&
    eqA 1782 (powArr 1782 dg[i]! 3) (idA 1782)) &&
  allLt 5 (fun i => allLt 5 fun j => commA 1782 dg[i]! dg[j]!) &&
  allLt 243 (fun k => allLt 243 fun k' => k == k' || !(eqA 1782 E[k]! E[k']!))


end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.SuzT
