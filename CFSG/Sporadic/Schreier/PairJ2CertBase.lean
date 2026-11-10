
module

public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Certificates.SchreierChainOrderGenerators
public import CFSG.Sporadic.J1.VecSpec
public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.Sporadic.Schreier.PairText
public import Certificates.Data.CFSGNative.PairSchreier.J2Data
public meta import CFSG.Sporadic.Schreier.PairText
public meta import Certificates.Data.CFSGNative.PairSchreier.J2Data
public meta import Certificates.Data.CFSGNative.J1.Vec
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Sporadic.Schreier.PairJ2CertInputs

@[expose] public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairText


@[expose] def j2BasisIdx : List ℕ := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 15]

@[expose] def j2Vec (i : ℕ) : Fin 14 → ZMod 5 := CFSG.Sporadic.J1.toV 5 14 j2Vectors[i]!

@[expose] def j2X : Set (Fin 14 → ZMod 5) := {v | ∃ i < 315, j2Vec i = v}

@[expose] def j2BaseFin : List (Fin 315) := [1, 0, 2]

@[expose] def j2StrongPerm (j : ℕ) : Equiv.Perm (Fin 315) := permOfArr 315 j2StrongArrs[j]!

@[expose] def j2Gen (k : ℕ) : Equiv.Perm (Fin 315) := j2StrongPerm k

@[expose] def j2Chain : RawSchreierDatum 315 :=
  RawSchreierDatum.ofArrays 315 (by decide) j2StrongArrs 2 (by simp [j2StrongArrs]) j2BaseFin
    (by decide) j2Words

@[expose] def j2P : Subgroup (Equiv.Perm (Fin 315)) := Subgroup.closure {j2Gen 0, j2Gen 1}


theorem rep_of_j2PermOK {t : Array ℕ} (h : j2PermOK t = true) : Rep 315 t (permOfArr 315 t) := by
  simp only [j2PermOK, Bool.and_eq_true] at h
  exact (rep_permOfArr h.2).1


theorem j2Chain_original_get (k : Fin j2Chain.originalCount) :
    j2Chain.original.get k = j2Gen k :=
  RawSchreierDatum.ofArrays_original_get k

theorem j2Chain_base : j2Chain.base.toList.map Fin.val = [1, 0, 2] := by
  rw [j2Chain, RawSchreierDatum.ofArrays_base_toList]
  rfl

theorem j2P_eq_original : j2P = j2Chain.originalSubgroup := by
  have e : j2Chain.original.toList = [j2Gen 0, j2Gen 1] := by
    apply List.ext_getElem (by simp [j2Chain, RawSchreierDatum.ofArrays])
    intro k h1 _
    have hk : k < j2Chain.originalCount := by simpa using h1
    rw [Vector.getElem_toList]
    have := j2Chain_original_get ⟨k, hk⟩
    rw [Vector.get] at this
    simp only [Fin.cast_mk] at this
    rw [show j2Chain.original[k] = j2Chain.original.toArray[k]'(by simpa using hk) from rfl, this]
    have hk2 : k < 2 := hk
    interval_cases k <;> rfl
  rw [j2P, RawSchreierDatum.originalSubgroup, e]
  congr 1
  ext g
  simp

end CFSG.Sporadic.Schreier
