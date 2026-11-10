module

public import Certificates.Data.Kernel.Tower.L3Q
public import Certificates.Data.Kernel.Tower.T2Sq
public import Certificates.Kernel.Tower.WrEChecks
public import Certificates.Kernel.Tower.L3OChecks
public import Certificates.Kernel.Tower.WrSData
import CFSG.Certificates.Kernel.Common.Each

public section

namespace Certificates.KernelTower

open Certificates.KernelTower

@[expose] noncomputable def ch36408_eq (e : Nat) : Bool :=
  icB (wrED e 0) (wrED e 2) (wrED e 3) (wrEP e 2) &&
    allB (wrEP e 10) fun k =>
      allB 16 (fun j => sqB (l3M (Nat.add (wrEP e 9) k)) (l3bc (Nat.add (wrEP e 9) k) j)
        (l3G (Nat.add (wrEP e 9) k)) (l3Im (Nat.add (wrEP e 9) k) j)
        (l3g2 (Nat.add (wrEP e 9) k) j) (wrX e)) &&
      cenB (l3M (Nat.add (wrEP e 9) k)) (l3bc (Nat.add (wrEP e 9) k)) (l3G (Nat.add (wrEP e 9) k))
        (wrED e 4) (l3Im (Nat.add (wrEP e 9) k)) (l3g2 (Nat.add (wrEP e 9) k)) 16

#kc_each ch36408_eq 0 12

@[expose] noncomputable def wrGL (a k : Nat) : Nat := l16 wrT2.b0 (Nat.add (Nat.mul 2 a) k)

@[expose] noncomputable def wrFE (a g : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 12
    (fun e acc => Bool.rec (motive := fun _ => Nat) acc e
      (Nat.beq (wrEP e 0) a && Nat.beq (wrEP e 1) g)) 12

@[expose] noncomputable def wrDP (DP a : Nat) : Bool :=
  allB 2 fun k => Nat.blt (wrFE a (wrGL a k)) 12 ||
    !Nat.beq (bit DP (Nat.add (Nat.mul 2 a) k)) 1

theorem ch36408_dp : allB 96 (wrDP wrT2.b1) = true := by decide +kernel


end Certificates.KernelTower
