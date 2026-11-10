module

public import Certificates.Data.CFSGNative.YGroups.DCE.EngineB
public import CFSG.YGroups.DCE.PermBSpec
public import CFSG.YGroups.DoubleCosetPoints
public import Batteries.Data.ByteArray
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.YGroups.DCE.B

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.YGroups.DCE


section Level

variable {E : EnvB}


end Level

def stabSub {G Eg Ω : Type*} [Group G] [Group Eg] [MulAction Eg Ω]
    (S : SymGen.Setup G Eg Ω) (g : G) : Subgroup Eg where
  carrier := {e | g * S.ψ e * g⁻¹ ∈ S.H}
  mul_mem' {a b} ha hb := by
    have := S.H.mul_mem ha hb
    rwa [show g * S.ψ a * g⁻¹ * (g * S.ψ b * g⁻¹) = g * S.ψ (a * b) * g⁻¹ by
      rw [map_mul]; group] at this
  one_mem' := by
    show g * S.ψ 1 * g⁻¹ ∈ S.H
    rw [map_one, mul_one, mul_inv_cancel]
    exact S.H.one_mem
  inv_mem' {a} ha := by
    have := S.H.inv_mem ha
    rwa [show (g * S.ψ a * g⁻¹)⁻¹ = g * S.ψ a⁻¹ * g⁻¹ by rw [map_inv]; group] at this

theorem mem_stabSub {G Eg Ω : Type*} [Group G] [Group Eg] [MulAction Eg Ω]
    (S : SymGen.Setup G Eg Ω) (g : G) (e : Eg) :
    e ∈ stabSub S g ↔ g * S.ψ e * g⁻¹ ∈ S.H :=
  Iff.rfl


end CFSG.YGroups.DCE.B

namespace CFSG.YGroups.DCE

open CFSG.Monster.B.Co2


end CFSG.YGroups.DCE
