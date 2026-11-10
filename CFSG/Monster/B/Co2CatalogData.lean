module

public import Lean.Data.Json.FromToJson.Basic
public import Lean.Data.Json.Parser

public section

namespace CFSG.Monster.B.Co2Catalog

open Lean (Json)


structure BridgeFile where
  purpose : String
  nativeAWord : List Int
  nativeBWord : List Int
  nativeRows : List (List Nat)
  catalogTransposeRows : List (List Nat)
  changeOfBasisRows : List Nat
  intertwinerDimension : Nat
  attempt : Nat
  deriving DecidableEq, Inhabited


@[expose] def bridgeRec : BridgeFile where
  purpose := "Original exact native-to-catalog Co2 matrix bridge proposal; no independent review."
  nativeAWord := [15]
  nativeBWord := [-2, -3, -9, -8, -9, -13, -11, -16, -21, -8, -9, -22, -24, -4, -2, -1, 2, 14, 2,
    14, 14, 23, 2, 9, 9, 21, 24, 18, 17, 13, 5, 15, 2, 14, 2, 14, 14, 23, 2, 9, 9, 21, 24, 18, 17,
    13, 5, 15, 2, 14, 2, 14, 14, 23, 2, 9, 9, 21, 24, 18, 17, 13, 5, 15, 1, 2, 4, 24, 22, 9, 8, 21,
    16, 11, 13, 9, 8, 9, 3, 2]
  nativeRows :=
    [[12318, 12317, 4, 12311, 12303, 442400, 1800256, 454815, 747807, 455199, 748575, 1060891,
      1058843, 1054747, 1079300, 1095684, 1128452, 1193988, 1325060, 1587204, 14363, 3160068],
     [1574232, 2813096, 786461, 2210002, 2317639, 1107934, 1472506, 1623393, 3233574, 145096,
      1046142, 2147565, 1889377, 1070516, 3391670, 665745, 3025201, 1670464, 1890518, 3198194,
      2410223, 3404192]]
  catalogTransposeRows :=
    [[2114050, 2114049, 1048584, 1048580, 415936, 3150720, 415888, 128, 3150496, 512, 1024, 2048,
      4096, 3473408, 16384, 917504, 3416064, 131072, 262144, 425984, 1048576, 2097152],
     [2097280, 2097154, 2097283, 3047424, 2621572, 3014664, 655360, 2621584, 2883584, 3014688,
      2228288, 2359552, 3015168, 2753536, 2361344, 3018752, 2097152, 2760704, 802816, 2621440,
      2686976, 1048576]]
  changeOfBasisRows := [2495974, 472725, 2177759, 823366, 3635269, 3623954, 5507, 2109435,
    2710470, 1032327, 3267302, 1170103, 2972347, 2142667, 3505457, 3222369, 1270289, 3351486,
    2379581, 2232114, 1774027, 24222]
  intertwinerDimension := 1
  attempt := 21

end CFSG.Monster.B.Co2Catalog
