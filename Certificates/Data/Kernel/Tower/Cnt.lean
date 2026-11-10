module

public import Certificates.Data.Kernel.Tower.Cls14
public import Certificates.Data.Kernel.Tower.Chunk

public section

namespace Certificates.KernelTower

@[expose] noncomputable def hmL (HL m : Nat) : Nat :=
  Nat.rec 0 (fun j acc => Nat.lor acc (Nat.shiftLeft 1 (l16 HL j))) m


@[expose] noncomputable def czHB (H CZ nl : Nat) : Bool :=
  allB nl fun l => Nat.beq (lane H 15 32767 l) (lane CZ 14 16383 l)


end Certificates.KernelTower
