module

public import Certificates.Data.CFSGNative.PSL3Four.L34Aut

public section

namespace CFSG.PSL3Four.Native

@[expose] def a₀T : Tab :=
  #[1, 5, 17, 9, 13, 0, 4, 3, 2, 7, 19, 11, 15, 6, 14, 18, 10, 8, 12, 16, 20, 22, 26, 34, 38,
    30, 21, 24, 23, 25, 29, 37, 41, 33, 28, 32, 36, 40, 27, 39, 31, 35]

@[expose] def b₀T : Tab :=
  #[0, 1, 3, 4, 2, 5, 8, 6, 7, 13, 16, 14, 15, 17, 20, 18, 19, 9, 12, 10, 11, 21, 22, 25, 23,
    24, 26, 28, 29, 27, 38, 40, 41, 39, 30, 32, 33, 31, 34, 36, 37, 35]

@[expose] def e9T (_ : Unit := ()) : Array Tab :=
  Array.ofFn (n := 9) fun k => comp 42 (powTab 42 a₀T (k.val / 3)) (powTab 42 b₀T (k.val % 3))


end CFSG.PSL3Four.Native
