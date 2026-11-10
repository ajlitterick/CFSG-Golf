module

public import Certificates.Data.CFSGNative.MonsterB.IntertwinerData

public section

namespace CFSG.Monster.B.Bin

set_option compiler.extract_closed false

@[noinline, expose] def seedMat (n : Nat) (s : String) : Mat :=
  matOfRows n (CFSG.Sporadic.SmallF2.Native.rowsOfPayload n s)

@[expose] def progStep (n : Nat) (R : Array Mat) (ins : Nat × Nat × Nat) : Array Mat :=
  R.set! ins.2.2 (mulP n (R.getD ins.1 #[]) (R.getD ins.2.1 #[]))

@[expose] def initRegs (n : Nat) (A B : Mat) : Array Mat :=
  #[idMat n, A, B, idMat n, idMat n, idMat n]

@[expose] def runProg (n : Nat) (A B : Mat) : Array Mat := max2Prog.foldl (progStep n) (initRegs n A B)


end CFSG.Monster.B.Bin
