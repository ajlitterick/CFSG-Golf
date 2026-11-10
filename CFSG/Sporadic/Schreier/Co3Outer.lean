module

public import CFSG.Sporadic.Schreier.Co3CertBase
public import CFSG.Sporadic.Schreier.Co3CertCheck

public noncomputable section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier.Co3.Native

theorem co3Field276_size (f : ℕ) : (co3Field276 f).size = (co3Lines276.getD f (0, 0)).2 := by
  rw [co3Field276, Array.size_ofFn]

theorem co3Field36_size (f : ℕ) : (co3Field36 f).size = (co3Lines36.getD f (0, 0)).2 := by
  rw [co3Field36, Array.size_ofFn]

theorem co3Field12_size (f : ℕ) : (co3Field12 f).size = (co3Lines12.getD f (0, 0)).2 := by
  rw [co3Field12, Array.size_ofFn]

@[expose] def co3TChain : RawSchreierDatum 276 :=
  RawSchreierDatum.ofArrays 276 (by decide) co3TArrs co3TGenCount
    (by rw [co3TArrs, co3Field276_size]; decide) (co3FinList 276 (by decide) co3TBase)
    (by decide) (wordsArr co3TGenCount co3TStrongCount co3TDerivations)

@[expose] def co3MChain : RawSchreierDatum 276 :=
  RawSchreierDatum.ofArrays 276 (by decide) co3MArrs co3MGenCount
    (by rw [co3MArrs, co3Field276_size]; decide) (co3FinList 276 (by decide) co3MBase)
    (by decide) (wordsArr co3MGenCount co3MStrongCount co3MDerivations)

@[expose] def co3M1Chain : RawSchreierDatum 276 :=
  RawSchreierDatum.ofArrays 276 (by decide) co3M1Arrs co3M1GenCount
    (by rw [co3M1Arrs, co3Field276_size]; decide) (co3FinList 276 (by decide) co3M1Base)
    (by decide) (wordsArr co3M1GenCount co3M1StrongCount co3M1Derivations)

@[expose] def co3MCommChain : RawSchreierDatum 276 :=
  RawSchreierDatum.ofArrays 276 (by decide) co3MCommArrs co3MCommGenCount
    (by rw [co3MCommArrs, co3Field276_size]; decide) (co3FinList 276 (by decide) co3MCommBase)
    (by decide) (wordsArr co3MCommGenCount co3MCommStrongCount co3MCommDerivations)

@[expose] def co3M1CommChain : RawSchreierDatum 276 :=
  RawSchreierDatum.ofArrays 276 (by decide) co3M1CommArrs co3M1CommGenCount
    (by rw [co3M1CommArrs, co3Field276_size]; decide)
    (co3FinList 276 (by decide) co3M1CommBase) (by decide)
    (wordsArr co3M1CommGenCount co3M1CommStrongCount co3M1CommDerivations)

@[expose] def co3JointChain : RawSchreierDatum 276 :=
  RawSchreierDatum.ofArrays 276 (by decide) co3JointArrs co3JointGenCount
    (by rw [co3JointArrs, co3Field276_size]; decide) (co3FinList 276 (by decide) co3JointBase)
    (by decide) (wordsArr co3JointGenCount co3JointStrongCount co3JointDerivations)

@[expose] def co3Sp36Chain : RawSchreierDatum 36 :=
  RawSchreierDatum.ofArrays 36 (by decide) co3Sp36Arrs co3Sp36GenCount
    (by rw [co3Sp36Arrs, co3Field36_size]; decide) (co3FinList 36 (by decide) co3Sp36Base)
    (by decide) (wordsArr co3Sp36GenCount co3Sp36StrongCount co3Sp36Derivations)

@[expose] def co3M36Chain : RawSchreierDatum 36 :=
  RawSchreierDatum.ofArrays 36 (by decide) co3M36Arrs co3M36GenCount
    (by rw [co3M36Arrs, co3Field36_size]; decide) (co3FinList 36 (by decide) co3M36Base)
    (by decide) (wordsArr co3M36GenCount co3M36StrongCount co3M36Derivations)

@[expose] def co3M112Chain : RawSchreierDatum 12 :=
  RawSchreierDatum.ofArrays 12 (by decide) co3M112Arrs co3M112GenCount
    (by rw [co3M112Arrs, co3Field12_size]; decide) (co3FinList 12 (by decide) co3M112Base)
    (by decide) (wordsArr co3M112GenCount co3M112StrongCount co3M112Derivations)

@[expose] def co3T : Subgroup (Equiv.Perm (Fin 276)) := co3TChain.originalSubgroup

@[expose] def co3M : Subgroup (Equiv.Perm (Fin 276)) := co3MChain.originalSubgroup

@[expose] def co3M1 : Subgroup (Equiv.Perm (Fin 276)) := co3M1Chain.originalSubgroup

@[expose] def co3DM : Subgroup (Equiv.Perm (Fin 276)) := co3MCommChain.originalSubgroup

@[expose] def co3L : Subgroup (Equiv.Perm (Fin 276)) := co3M1CommChain.originalSubgroup

@[expose] def co3JointG : Subgroup (Equiv.Perm (Fin 276)) := co3JointChain.originalSubgroup

@[expose] def co3X36 : Subgroup (Equiv.Perm (Fin 36)) := co3Sp36Chain.originalSubgroup

@[expose] def co3XM : Subgroup (Equiv.Perm (Fin 36)) := co3M36Chain.originalSubgroup

@[expose] def co3X12 : Subgroup (Equiv.Perm (Fin 12)) := co3M112Chain.originalSubgroup

@[expose] def co3Z : Equiv.Perm (Fin 276) := permOfArr 276 co3ZArr

@[expose] def co3Tt : Equiv.Perm (Fin 276) := permOfArr 276 co3TtArr

@[expose] def co3D0Gen (k : ℕ) : Equiv.Perm (Fin 276) := permOfArr 276 co3D0Arrs[k]!

@[expose] def co3D0 : Subgroup (Equiv.Perm (Fin 276)) :=
  Subgroup.closure {g | ∃ k < 5, co3D0Gen k = g}

@[expose] def co3Iz : List (Fin 276) := co3FinList 276 (by decide) co3IzNat

@[expose] def co3It : List (Fin 276) := co3FinList 276 (by decide) co3ItNat

@[expose] def co3Csp : Equiv.Perm (Fin 36) := permOfArr 36 co3CspArr

@[expose] def co3C12 : Equiv.Perm (Fin 12) := permOfArr 12 co3C12Arr


abbrev Co3V6 : Type := Fin 3 ⊕ Fin 3 → ZMod 2

@[expose] def co3Coord6 (i : Fin 6) : Fin 3 ⊕ Fin 3 :=
  if h : (i : ℕ) < 3 then .inl ⟨i, h⟩ else .inr ⟨i - 3, by omega⟩

@[expose] def co3Idx6 : Fin 3 ⊕ Fin 3 → ℕ
  | .inl i => i
  | .inr i => i + 3

@[expose] def co3Sp6Form (a : ℕ) (x : Co3V6) : ZMod 2 :=
  ∑ i : Fin 3, x (.inl i) * x (.inr i) +
    ∑ i : Fin 6, (if a.testBit i then 1 else 0) * x (co3Coord6 i)

@[expose] def co3A : List ℕ := co3Sp6Forms

theorem co3Lines276_le : ∀ f < 11,
    (co3Lines276.getD f (0, 0)).1 + (co3Lines276.getD f (0, 0)).2 ≤ 111 := by
  decide

theorem co3Lines36_le : ∀ f < 3,
    (co3Lines36.getD f (0, 0)).1 + (co3Lines36.getD f (0, 0)).2 ≤ 83 := by
  decide

theorem co3Lines12_le : ∀ f < 2,
    (co3Lines12.getD f (0, 0)).1 + (co3Lines12.getD f (0, 0)).2 ≤ 14 := by
  decide

theorem isInvA_co3Field276
    {f k : ℕ} (hf : f < 11) (hk : k < (co3Field276 f).size) :
    isInvA 276 (co3Field276 f)[k]! (invCand 276 (co3Field276 f)[k]!) = true := by
  rw [co3Field276_size] at hk
  rw [co3Field276, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  refine co3Layout_check.2.2.2.2.1 _ ?_
  have := co3Lines276_le f hf
  omega

theorem isInvA_co3Field36
    {f k : ℕ} (hf : f < 3) (hk : k < (co3Field36 f).size) :
    isInvA 36 (co3Field36 f)[k]! (invCand 36 (co3Field36 f)[k]!) = true := by
  rw [co3Field36_size] at hk
  rw [co3Field36, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  refine co3Layout_check.2.2.2.2.2.1 _ ?_
  have := co3Lines36_le f hf
  omega

theorem isInvA_co3Field12
    {f k : ℕ} (hf : f < 2) (hk : k < (co3Field12 f).size) :
    isInvA 12 (co3Field12 f)[k]! (invCand 12 (co3Field12 f)[k]!) = true := by
  rw [co3Field12_size] at hk
  rw [co3Field12, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]
  refine co3Layout_check.2.2.2.2.2.2.1 _ ?_
  have := co3Lines12_le f hf
  omega

theorem co3Field276_size' (f : ℕ) {m : ℕ} (h : (co3Lines276.getD f (0, 0)).2 = m) :
    (co3Field276 f).size = m := by
  rw [co3Field276_size, h]

theorem co3Field36_size' (f : ℕ) {m : ℕ} (h : (co3Lines36.getD f (0, 0)).2 = m) :
    (co3Field36 f).size = m := by
  rw [co3Field36_size, h]

theorem co3Field12_size' (f : ℕ) {m : ℕ} (h : (co3Lines12.getD f (0, 0)).2 = m) :
    (co3Field12 f).size = m := by
  rw [co3Field12_size, h]


end CFSG.Sporadic.Schreier.Co3
