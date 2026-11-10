
module

public import CFSG.Sporadic.HNOddCore.SylABase
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public meta import CFSG.Sporadic.HNOddCore.QCheck
public meta import Std.Data.HashMap
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public meta import Certificates.Data.CFSGNative.Perm.Chain

@[expose] public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

@[irreducible] def idxMap : Std.HashMap (Array ℕ) ℕ := pIdx pE

theorem idxMap_eq : idxMap = pIdx pE := by unfold idxMap; rfl

@[irreducible] def csArr : Array (Array ℕ × Array ℕ × Array ℕ) :=
  pReps.map fun r => conjOrbit (pIdx pE) pE InvData.pgenPerms (pinvs 800 InvData.pgenPerms) r

theorem csArr_eq : csArr = pReps.map fun r =>
    conjOrbit (pIdx pE) pE InvData.pgenPerms (pinvs 800 InvData.pgenPerms) r := by
  unfold csArr; rfl

@[irreducible] def mkArr : Array ℕ := classMarks (csArr.map (·.1))

theorem mkArr_eq : mkArr = classMarks (csArr.map (·.1)) := by unfold mkArr; rfl

theorem conj_mem_of_closure {G : Type*} [Group G] [Finite G] {S T : Set G}
    (hT : ∀ g ∈ T, ∀ x ∈ S, g * x * g⁻¹ ∈ S) :
    ∀ g ∈ Subgroup.closure T, ∀ x ∈ S, g * x * g⁻¹ ∈ S := by
  have hmul : ∀ g h : G, (∀ x ∈ S, g * x * g⁻¹ ∈ S) → (∀ x ∈ S, h * x * h⁻¹ ∈ S) →
      ∀ x ∈ S, g * h * x * (g * h)⁻¹ ∈ S := fun g h hg hh x hx => by
    have := hg _ (hh x hx)
    rwa [mul_inv_rev, show g * h * x * (h⁻¹ * g⁻¹) = g * (h * x * h⁻¹) * g⁻¹ by group]
  have hpow : ∀ g : G, (∀ x ∈ S, g * x * g⁻¹ ∈ S) →
      ∀ k : ℕ, ∀ x ∈ S, g ^ k * x * (g ^ k)⁻¹ ∈ S := by
    intro g hg k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih hg
  let M : Subgroup G :=
    { carrier := {g | ∀ x ∈ S, g * x * g⁻¹ ∈ S}
      mul_mem' := fun {g h} hg hh => hmul g h hg hh
      one_mem' := fun x hx => by simpa using hx
      inv_mem' := fun {g} hg => by
        have e : g⁻¹ = g ^ (orderOf g - 1) := by
          rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ,
            Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
        show ∀ x ∈ S, g⁻¹ * x * g⁻¹⁻¹ ∈ S
        rw [e]
        exact hpow g hg _ }
  have hle : Subgroup.closure T ≤ M := by
    rw [Subgroup.closure_le]
    exact hT
  exact fun g hg => hle hg

abbrev clsL (c : ℕ) : Array ℕ := csArr[c]!.1

@[expose] def repPerm (c : ℕ) : Perm (Fin 800) := ePerm pReps[c]!

@[expose] def classSet (c : ℕ) : Set (Perm (Fin 800)) :=
  {x | ∃ j < (clsL c).size, ePerm (clsL c)[j]! = x}


end CFSG.Sporadic.HNOddCore
