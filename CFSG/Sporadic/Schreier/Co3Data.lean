module

public section

namespace CFSG.Sporadic.Schreier.Co3

@[expose] def co3Perm276Text : String :=
  include_str "../../../Certificates/Data/CFSGNative/Co3Schreier/co3-perm276.txt"

@[expose] def co3Perm36Text : String :=
  include_str "../../../Certificates/Data/CFSGNative/Co3Schreier/co3-perm36.txt"

@[expose] def co3Perm12Text : String :=
  include_str "../../../Certificates/Data/CFSGNative/Co3Schreier/co3-perm12.txt"

@[expose] def co3FormsText : String :=
  include_str "../../../Certificates/Data/CFSGNative/Co3Schreier/co3-forms.txt"

@[expose] def co3Lines276 : List (Nat × Nat) :=
  [(0, 14), (14, 14), (28, 1), (29, 1), (30, 5), (35, 10), (45, 14), (59, 11), (70, 8), (78, 8),
    (86, 25)]

@[expose] def co3Lines36 : List (Nat × Nat) :=
  [(0, 66), (66, 16), (82, 1)]

@[expose] def co3Lines12 : List (Nat × Nat) :=
  [(0, 13), (13, 1)]


@[expose] def co3DiffIdx : List Nat :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 18, 19, 20, 21, 22, 27]

@[expose] def co3CoprimeWord : List Int :=
  [-1, -2, -2, 1, -1, -2, -1, -2, -2, 1, 2, 2]


@[expose] def co3ChainGenCount : Nat := 2

@[expose] def co3ChainStrongCount : Nat := 14

@[expose] def co3ChainBase : List Nat := [0, 1, 2, 3, 4, 5, 6]

@[expose] def co3ChainDerivations : List (List Int) :=
  [[-2, -1, 2, 2, 1, 2], [-1, 3, 1, 3, 1], [3, -1, -1, 3, -1, 3, 1, 3, 1, 1, 3], [-1, -1, 3, -1,
    -1, 3, -1, 3, -1, -2, -2, -2, -1, 2, 2, 1, 2, 2, 2], [5, 6, 5], [-4, -4, 6, 4, 4], [-4, 5,
    6, 5, 6, 4, 4, 6], [-9, 7, 9, 9, 7], [-10, 8, 10], [10, 8, 10, 8], [11, 12, 8, -10, -10, 8,
    10, 10, 8], [8, -10, -10, -10, -10, -9, -9, -9, 8, -4, 6, 5, 6, -4, -4, 6, -4, -4, -1, 6,
    -1, -1, 3, 6, -2, -2, -1, -2, -1, -2, -1, 2, 1, 2, 1, 2, 1, 2, 2]]

@[expose] def co3CoprimeGenCount : Nat := 2

@[expose] def co3CoprimeStrongCount : Nat := 14

@[expose] def co3CoprimeBase : List Nat := [0, 1, 2, 3, 4, 5, 6]

@[expose] def co3CoprimeDerivations : List (List Int) :=
  [[-2, -1, -2, -2, -1, 2, 2, 2, 1, 2], [-1, -3, -1, -1, -3, 1, 1, 3, 3, 1], [-1, -1, -3, -3,
    -1, 3, 1, 1, 3, 3], [-4, 5, 4], [-5, -4, -4, -4, 5, 4, 5, 4, 4], [-6, -6, 7, 7, 6], [-7, -6,
    -6, -7, 6, 7, 7, 6, 6], [-6, -7, -6, -7, -6, -7, -7, -6, -5, -4, -5, -4, 5, 4, 5, 4, 5],
    [-10, -9, 10, 9, 8], [-7, 10, 10, 7], [8, 12, 8, 9], [-10, -9, -7, -7, -10, -6, -5, -5, -4,
    -4, -5, -4, -3, -1, -3, -3, -1, -3, -3, -2, -1, -1, 2, 1, 2, 1, 1, 2]]


@[expose] def co3TGenCount : Nat := 8

@[expose] def co3TStrongCount : Nat := 10

@[expose] def co3TBase : List Nat := [0, 1, 2]

@[expose] def co3TDerivations : List (List Int) :=
  [[1, 1, 6], [1, 1, 7]]

@[expose] def co3MGenCount : Nat := 7

@[expose] def co3MStrongCount : Nat := 14

@[expose] def co3MBase : List Nat := [0, 1, 2, 3]

@[expose] def co3MDerivations : List (List Int) :=
  [[7, 4, -3, 5, -7], [7, 3, -4, 5, -7], [7, 4, 4, -7], [7, -4, 5, -7], [-6, 4, 3, -5, 7, -5,
    7], [4, 4, 5], [1, -4, 3, 6]]

@[expose] def co3M1GenCount : Nat := 6

@[expose] def co3M1StrongCount : Nat := 11

@[expose] def co3M1Base : List Nat := [0, 1, 3, 4]

@[expose] def co3M1Derivations : List (List Int) :=
  [[1, 2, 2, 3, -5, 2], [6, 3, -5, 2, -6, -5, 2], [3, 6, 2, 3, -5, -6], [-2, 5], [6, 5, -4, 5,
    -2, -6]]

@[expose] def co3MCommGenCount : Nat := 4

@[expose] def co3MCommStrongCount : Nat := 8

@[expose] def co3MCommBase : List Nat := [0, 1, 2, 3]

@[expose] def co3MCommDerivations : List (List Int) :=
  [[-2, 3, 4, -2, 1, -3, 4, -2, -4, -2, 1], [1, 4, 2, 4, 2, 4, 2, 1, -3, 4, 3, -4, 3], [4, 3, 1,
    2, 4, -3, 1], [1, 4, 3, -2, 4, -3, 1, 3, -2, -4, 3, -2]]

@[expose] def co3M1CommGenCount : Nat := 3

@[expose] def co3M1CommStrongCount : Nat := 8

@[expose] def co3M1CommBase : List Nat := [0, 1, 3, 4]

@[expose] def co3M1CommDerivations : List (List Int) :=
  [[1, 3, 1, 2, 3, 2, -3, -2, 3], [1, 2, 3, 1, -2, -3, -2, -2, 3], [-2, -1, 3, -1, 3, 1, 2], [1,
    -2, -3, 1, -2, -3], [-2, 1, 2, 1, 3, -1, 3]]

@[expose] def co3JointGenCount : Nat := 13

@[expose] def co3JointStrongCount : Nat := 25

@[expose] def co3JointBase : List Nat := [0, 1, 2, 3, 4, 5, 6]

@[expose] def co3JointDerivations : List (List Int) :=
  [[-9, 12], [2, 9, 2], [-14, -14, 15, 14, 14], [10, -14, -15, 10, 15, 14, 15, 10], [-17, 16,
    17, 16, 16], [-17, -17, 16, 17, 16, 16, 16], [-18, -19, 18, 18, 18], [18, 18, 19, 18, 18],
    [-20, -21, 20, 20, 20], [-22, -22, -21, 20, 20, 21], [-21, -21, -20, 21, 21, 21], [-21, -21,
    -20, -19, -18, -18, 19, 18, 19, 18, 18]]

@[expose] def co3Sp36GenCount : Nat := 63

@[expose] def co3Sp36StrongCount : Nat := 66

@[expose] def co3Sp36Base : List Nat := [0, 1, 2, 4, 8, 12]

@[expose] def co3Sp36Derivations : List (List Int) :=
  [[36, 60, 52, 44], [36, 44, 18, 30, 26, 22], [36, 52, 18, 22, 9, 15, 13, 11]]

@[expose] def co3M36GenCount : Nat := 6

@[expose] def co3M36StrongCount : Nat := 16

@[expose] def co3M36Base : List Nat := [0, 1, 2, 8, 12, 4]

@[expose] def co3M36Derivations : List (List Int) :=
  [[-3, 4, 2], [-5, -2, 4, 5], [1, 8, 1], [8, 1, 8], [-7, 8, 1, 8, 7], [-5, 6, 5], [9, 11, -7,
    -7, 12, 7], [11, -13, 10, 13], [10, -13, 9, -13, 9, 10, 13, 9], [14, 15, 14]]

@[expose] def co3M112GenCount : Nat := 5

@[expose] def co3M112StrongCount : Nat := 13

@[expose] def co3M112Base : List Nat := [0, 1, 2, 3, 4]

@[expose] def co3M112Derivations : List (List Int) :=
  [[2, 1, 1], [-4, 2, 1], [-5, 3, 1], [8, 6], [-9, 7, 9], [-7, -7, -7, 9, 7, 7], [-10, 11, 10],
    [-10, -10, -7, -9, -7, 9, 9, 7]]

@[expose] def co3MCommPairs : List (Nat × Nat) :=
  [(2, 5), (2, 6), (2, 7), (3, 4)]

@[expose] def co3M1CommPairs : List (Nat × Nat) :=
  [(2, 5), (2, 6), (3, 6)]

@[expose] def co3IzNat : List Nat :=
  [9, 19, 28, 43, 45, 49, 54, 55, 62, 80, 118, 121, 129, 141, 144, 151, 158, 165, 168, 170, 173,
    176, 192, 210, 214, 223, 226, 228, 232, 235, 242, 244, 253, 260, 261, 269]

@[expose] def co3ItNat : List Nat :=
  [35, 41, 43, 79, 80, 108, 123, 126, 208, 209, 253, 260]

@[expose] def co3Sp6Forms : List Nat :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 14, 16, 17, 20, 21, 24, 27, 28, 31, 32, 33, 34, 35, 40,
    42, 45, 47, 48, 49, 54, 55, 56, 59, 61, 62]


end CFSG.Sporadic.Schreier.Co3
