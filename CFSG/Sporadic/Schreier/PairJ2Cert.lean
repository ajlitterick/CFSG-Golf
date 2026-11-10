
module

public import CFSG.Sporadic.Schreier.PairJ2CertBase

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
public import Certificates.Certificate2233
public import Certificates.Certificate2233Base

public noncomputable section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.Schreier.PairText

theorem j2CertOK_eq : j2CertOK = true :=
  Certificates.certificate2233

theorem j2CertOK_parts :
    j2Vectors.size = 315 ∧ (∀ i < 315, CFSG.Sporadic.J1.Native.wfV 5 14 j2Vectors[i]! = true) ∧
    (∀ j < 7, j2PermOK j2StrongArrs[j]! = true) ∧
    (∀ j < 7, isInvA 315 j2StrongArrs[j]! (rawInvs 315 j2StrongArrs)[j]! = true) ∧
    (j2Sylows.toList.map fun e => e.prime) = [2, 3, 5, 7] ∧
    (j2Sylows.toList.map fun e => e.gens.size) = [7, 3, 2, 1] ∧
    (j2Sylows.toList.map fun e => e.records.size) = [35, 13, 6, 1] ∧
    ∀ e < j2Sylows.size, (j2Sylows[e]!.gens.all j2PermOK && j2Sylows[e]!.records.all j2RecordOK)
      = true := by
  have h := j2CertOK_eq
  simp only [j2CertOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, -⟩, h3⟩, h4⟩, -⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, fun i hi => allLt_spec h2 hi, fun j hj => allLt_spec h3 hj,
    fun j hj => allLt_spec h4 hj, h5, h6, h7, fun e he => ?_⟩
  rw [Array.all_eq_true] at h8
  rw [getElem!_pos j2Sylows e he]
  exact h8 e he


theorem rep_j2StrongPerm {j : ℕ} (hj : j < 7) : Rep 315 j2StrongArrs[j]! (j2StrongPerm j) :=
  rep_of_j2PermOK (j2CertOK_parts.2.2.1 j hj)


end CFSG.Sporadic.Schreier
