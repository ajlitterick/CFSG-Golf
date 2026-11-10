
module

public import CFSG.Certificates.NativeSchreierArrays
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4
public import CFSG.Monster.B.Fischer.Fi22OuterArrays

public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Fischer

@[expose] def fi22OuterPerm3510 (L : ℕ) : Equiv.Perm (Fin 3510) :=
  permOfArr 3510 (fi22OuterArr3510 L)

@[expose] def fi22OuterPerm693 (L : ℕ) : Equiv.Perm (Fin 693) :=
  permOfArr 693 (fi22OuterArr693 L)


@[expose] def fi22FinList (n : ℕ) (hn : 0 < n) (b : List ℕ) : List (Fin n) :=
  b.map fun x => ⟨x % n, Nat.mod_lt _ hn⟩

@[expose] def fi22OuterChainM : RawSchreierDatum 3510 :=
  RawSchreierDatum.ofArrays 3510 (by decide) (fi22OuterStrong3510 3) fi22OuterMGenCount
    (by rw [fi22OuterStrong3510, Array.size_ofFn]; decide)
    (fi22FinList 3510 (by decide) fi22OuterMBase) (by decide)
    (fi22WordsArr fi22OuterMGenCount 17 fi22OuterMDerivations)

@[expose] def fi22OuterChainT : RawSchreierDatum 3510 :=
  RawSchreierDatum.ofArrays 3510 (by decide) (fi22OuterStrong3510 4) fi22OuterTGenCount
    (by rw [fi22OuterStrong3510, Array.size_ofFn]; decide)
    (fi22FinList 3510 (by decide) fi22OuterTBase) (by decide)
    (fi22WordsArr fi22OuterTGenCount 13 fi22OuterTDerivations)


@[expose] def fi22OuterChainUnitary : RawSchreierDatum 693 :=
  RawSchreierDatum.ofArrays 693 (by decide) (fi22OuterStrong693 2) fi22OuterUnitaryGenCount
    (by rw [fi22OuterStrong693, Array.size_ofFn]; decide)
    (fi22FinList 693 (by decide) fi22OuterUnitaryBase) (by decide)
    (fi22WordsArr fi22OuterUnitaryGenCount 49 fi22OuterUnitaryDerivations)

@[expose] def fi22OuterChainM693 : RawSchreierDatum 693 :=
  RawSchreierDatum.ofArrays 693 (by decide) (fi22OuterStrong693 3) fi22OuterM693GenCount
    (by rw [fi22OuterStrong693, Array.size_ofFn]; decide)
    (fi22FinList 693 (by decide) fi22OuterM693Base) (by decide)
    (fi22WordsArr fi22OuterM693GenCount 15 fi22OuterM693Derivations)


@[expose] def fi22OuterM : Subgroup (Equiv.Perm (Fin 3510)) := fi22OuterChainM.originalSubgroup

@[expose] def fi22OuterT : Subgroup (Equiv.Perm (Fin 3510)) := fi22OuterChainT.originalSubgroup

@[expose] def fi22OuterX : Subgroup (Equiv.Perm (Fin 693)) :=
  fi22OuterChainUnitary.originalSubgroup

@[expose] def fi22OuterField (f k : ℕ) : Equiv.Perm (Fin 3510) :=
  fi22OuterPerm3510 (fi22OuterLine3510 f k)


@[expose] def fi22OuterZ : Equiv.Perm (Fin 3510) := fi22OuterField 1 0


@[expose] def fi22OuterCu : Equiv.Perm (Fin 693) := fi22OuterPerm693 (fi22OuterLine693 0 0)


@[expose] def fi22OuterXRep (i : ℕ) : Equiv.Perm (Fin 3510) := fi22OuterField 6 i

@[expose] def fi22OuterU (j : ℕ) : Equiv.Perm (Fin 3510) := fi22OuterField 7 j

@[expose] def fi22OuterH (j : ℕ) : Equiv.Perm (Fin 3510) := fi22OuterField 8 j


@[expose] def fi22F4 (c : ℕ) : F4 := ⟨⟨c % 4, Nat.mod_lt _ (by decide)⟩⟩

@[expose] def fi22UnitaryPoint (k : ℕ) : Fin 6 → F4 :=
  fun i => fi22F4 (codeAt fi22OuterUnitaryPoints (6 * k + i))

@[expose] def fi22TransvectionVector (k : ℕ) : Fin 6 → F4 :=
  fun i => fi22F4 (codeAt fi22OuterTransvectionVectors (6 * k + i))


@[expose] def fi22Herm (v w : Fin 6 → F4) : F4 := ∑ i, v i ^ 2 * w i

@[expose] def fi22Normalize (v : Fin 6 → F4) : Fin 6 → F4 :=
  match (List.finRange 6).find? (fun i => decide (v i ≠ 0)) with
  | some i => (v i)⁻¹ • v
  | none => v

end CFSG.Monster.B.Fischer
